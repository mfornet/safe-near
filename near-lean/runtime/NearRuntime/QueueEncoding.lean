import NearRuntime.ReceiptEncoding
import NearRuntime.Fees

/-! Native queue columns for represented runtime state. Logical IDs alone do
not determine native hashes, data ownership, receipt formats or persisted queue
indices. The context supplies those facts; missing facts fail closed. Native
output-derived context is not a substitute for execution identity registration. -/
namespace Near.QueueEncoding

structure DataIdentity where
  id : DataId
  hash : NativeIdentity.Hash
  receiver : AccountId

inductive StorageForm
  | receipt
  | storedV0 (gas size : Nat)
  | storedV1 (gas size : Nat)
  /-- A newly enqueued receipt: V1 wrapper, current congestion gas and Borsh size. -/
  | newStored

structure Delayed where
  firstIndex : Nat
  forms : List StorageForm

structure Context where
  receipts : NativeIdentity.Bindings := []
  data : List DataIdentity := []
  formats : List (ReceiptId × ReceiptEncoding.ActionFormat) := []
  /-- None is an absent queue header; Some also preserves empty advanced queues. -/
  delayed : Option Delayed := none

private def unsigned (width value : Nat) : Except String Bytes := do
  unless value < 2 ^ (8 * width) do throw s!"integer exceeds u{8 * width}"
  return (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

private def unique [BEq α] (name : String) (values : List α) : Except String Unit := do
  unless values.eraseDups.length == values.length do throw s!"duplicate {name}"

private def ownedKey (tag : UInt8) (owner : AccountId) (hash : NativeIdentity.Hash) : Except String Bytes := do
  unless Wasm.Near.validAccountIdBytes owner.toUTF8.toList do throw "invalid queue receiver"
  return [tag] ++ owner.toUTF8.toList ++ [44] ++ (← NativeIdentity.checkedHash hash)

private def dataIdentity (context : Context) (id : DataId) : Except String DataIdentity := do
  let some identity := context.data.find? (·.id == id) | throw "data identity ownership is unavailable"
  return identity

private def checkOwner (context : Context) (id : DataId) (receiver : AccountId) : Except String Unit := do
  unless (← dataIdentity context id).receiver == receiver do throw "data identity receiver mismatch"

/-- Encode one receipt with the same identity, format and data-owner checks as queue records. -/
def receiptBytes (context : Context) (codes : List (String × Bytes)) (value : Receipt) : Except String Bytes := do
  let some format := Assoc.lookup context.formats value.receiptId | throw "receipt action format is unavailable"
  match value.receipt with
  | .data payload => checkOwner context payload.dataId value.receiverId
  | .action payload =>
    for id in payload.inputDataIds do checkOwner context id value.receiverId
    for output in payload.outputDataReceivers do checkOwner context output.dataId output.receiverId
  ReceiptEncoding.encode context.receipts (context.data.map fun value => (value.id, value.hash)) codes format value

/-- Newly stored ordinary receipts carry the native prepaid execution budget.
Delegate actions are not represented; their additional prepaid send fees do not
arise here. Data receipts carry zero congestion gas. This is not execution burn. -/
def congestionGas (cfg : Wasm.Near.RuntimeConfig) (receipt : Receipt) : Nat :=
  match receipt.receipt with
  | .data _ => 0
  | .action payload =>
    Fees.receiptGasBudget cfg receipt.receiverId payload.actions

private def storedBytes (cfg : Option Wasm.Near.RuntimeConfig) (form : StorageForm)
    (receipt : Receipt) (bytes : Bytes) : Except String Bytes := do
  let (version, gas, size) ← match form with
    | .receipt => return bytes
    | .storedV0 gas size => pure (0, gas, size)
    | .storedV1 gas size => pure (1, gas, size)
    | .newStored => do
      let some cfg := cfg | throw "new stored receipt requires runtime config"
      pure (1, congestionGas cfg receipt, bytes.length)
  return [255, 255, UInt8.ofNat version] ++ bytes ++ (← unsigned 8 gas) ++ (← unsigned 8 size)

/-- Queue-only entries. Pending counts are serialized as stored, never repaired
from receipt inputs. Structural ambiguity (orphans, aliases, missing ownership,
duplicate keys or inconsistent queue lengths) is rejected. -/
def queues (state : ChainState) (codes : List (String × Bytes)) (context : Context)
    (cfg : Option Wasm.Near.RuntimeConfig := none) : Except String (List (Bytes × Bytes)) := do
  NativeIdentity.validate context.receipts
  NativeIdentity.validate (context.data.map fun data => (data.id, data.hash))
  unique "receipt format" (context.formats.map Prod.fst)
  for data in context.data do
    let _ ← ownedKey 3 data.receiver data.hash
  unique "postponed receipt" (state.postponed.map Prod.fst)
  unique "pending data count" (state.pendingDataCount.map Prod.fst)
  unique "postponed data id" (state.postponedByData.map Prod.fst)
  unique "received data id" (state.receivedData.map Prod.fst)
  let mut entries := []
  for (id, receipt) in state.postponed do
    unless id == receipt.receiptId do throw "postponed receipt id mismatch"
    unless receipt.receipt matches .action _ do throw "postponed receipt must be an action"
    let hash ← NativeIdentity.resolve context.receipts id
    entries := entries ++ [(← ownedKey 6 receipt.receiverId hash, ← receiptBytes context codes receipt)]
  for (id, count) in state.pendingDataCount do
    let some receipt := Assoc.lookup state.postponed id | throw "pending count has no postponed receiver"
    entries := entries ++ [(← ownedKey 5 receipt.receiverId (← NativeIdentity.resolve context.receipts id), ← unsigned 4 count)]
  for (data, id) in state.postponedByData do
    let some receipt := Assoc.lookup state.postponed id | throw "postponed data link has no receipt"
    let identity ← dataIdentity context data
    checkOwner context data receipt.receiverId
    entries := entries ++ [(← ownedKey 4 identity.receiver identity.hash, ← NativeIdentity.resolve context.receipts id)]
  for (id, value) in state.receivedData do
    let identity ← dataIdentity context id
    entries := entries ++ [(← ownedKey 3 identity.receiver identity.hash, ← ReceiptEncoding.receivedData value)]
  match context.delayed with
  | none => unless state.delayed.isEmpty do throw "delayed queue context is unavailable"
  | some queue =>
    unless queue.forms.length == state.delayed.length do throw "delayed storage form count mismatch"
    let first ← unsigned 8 queue.firstIndex
    let next ← unsigned 8 (queue.firstIndex + state.delayed.length)
    entries := entries ++ [([7], first ++ next)]
    for ((receipt, form), offset) in (state.delayed.zip queue.forms).zipIdx do
      let bytes ← receiptBytes context codes receipt
      entries := entries ++ [([7] ++ (← unsigned 8 (queue.firstIndex + offset)), ← storedBytes cfg form receipt bytes)]
  unique "encoded queue key" (entries.map Prod.fst)
  return entries

/-- Combine typed account state and typed queue state. Opaque shard columns are
still outside the represented state; this does not claim an original shard root. -/
def encode (state : ChainState) (codes : List (String × Bytes)) (context : Context)
    (cfg : Option Wasm.Near.RuntimeConfig := none) : Except String (List (Bytes × Bytes)) := do
  let accountState := { state with
    postponed := []
    pendingDataCount := []
    postponedByData := []
    receivedData := []
    delayed := [] }
  let accounts ← StateEncoding.encode accountState codes
  let queues ← queues state codes context cfg
  return accounts ++ queues

end Near.QueueEncoding
