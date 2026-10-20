import ChainReplay.Encode
import ChainReplay.QueueContext
import NearRuntime.TransactionRegistry

/-! Execute the existing chain transition and register identities at their
observed births. Original transaction block hashes are explicit inputs;
generated native receipt/data hashes and queue metadata are outputs only.
The derived receipt bindings also supply native action randomness before VM execution. -/
namespace ChainReplay.Registered
open Lean Near

def formJson : QueueEncoding.StorageForm → Json
  | .receipt => obj [kind "receipt"]
  | .newStored => obj [kind "newStored"]
  | .storedV0 gas size => obj [kind "storedV0", ("gas", toJson gas), ("size", toJson size)]
  | .storedV1 gas size => obj [kind "storedV1", ("gas", toJson gas), ("size", toJson size)]

def contextJson (context : QueueEncoding.Context) : Json := obj [
  ("receiptIds", toJson (context.receipts.map fun (id, hash) => toJson [toJson id, bytesJson hash])),
  ("dataIds", toJson (context.data.map fun data => obj [
    ("id", toJson data.id), ("hash", bytesJson data.hash), ("receiverId", toJson data.receiver)])),
  ("actionFormats", toJson (context.formats.map fun (id, format) => toJson [toJson id,
    toJson (if format == ReceiptEncoding.ActionFormat.v2 then "v2" else "legacy")])),
  ("delayed", toJson (context.delayed.map fun delayed => obj [
    ("firstIndex", toJson delayed.firstIndex), ("forms", toJson (delayed.forms.map formJson))]))]

def encodeReceipt (codes : List (String × Bytes)) (context : QueueEncoding.Context) (receipt : Receipt) : Result Json := do
  let bytes ← QueueEncoding.receiptBytes context codes receipt
  pure (obj [("id", toJson receipt.receiptId), ("bytes", bytesJson bytes)])

def transactionIdentitiesJson (attempts : List TransactionRegistry.Attempt) : Json :=
  toJson (attempts.map fun attempt => obj [
    ("index", toJson attempt.index), ("bodySize", toJson attempt.body.length), ("hash", bytesJson attempt.hash),
    ("receiptId", toJson (attempt.receipt.map (·.receiptId))),
    ("receiptHash", toJson (attempt.receiptHash.map bytesJson))])

def birthsJson (births : List ReceiptIdentityBirth) : Json := toJson (births.map fun birth => obj [
  ("parent", toJson birth.parent), ("children", toJson birth.children),
  ("vmActions", toJson (birth.vmActions.map fun action => obj [
    ("actionIndex", toJson action.actionIndex), ("receipts", toJson action.receipts), ("data", toJson action.data)]))])

def run (protocol : Nat) (cfg : Wasm.Near.RuntimeConfig) (codes : Catalogue) (initial : Snapshot)
    (context : QueueEncoding.Context) (blocks : List Block) (hashes : List (List NativeIdentity.Hash)) : Result Json := do
  unless hashes.length == blocks.length do throw "transaction block-hash batch count mismatch"
  let catalogue := codes.map fun code => (code.code.hash, code.bytes)
  let initialEntries ← QueueEncoding.encode initial.state catalogue context (some cfg)
  let _ ← initial.pending.mapM (encodeReceipt catalogue context)
  let entriesJson (entries : List (Bytes × Bytes)) :=
    toJson (entries.map fun (key, value) => toJson [bytesJson key, bytesJson value])
  let finish (snapshot : Snapshot) (trace : List Json) (stop : String) (unrun : Nat) (extra : List (String × Json) := []) :=
    obj ([("formatVersion", toJson (1 : Nat)), ("protocolVersion", toJson protocol),
      ("model", toJson "near-lean-chain"), ("initialState", stateJson initial.state),
      ("initialPendingReceipts", toJson (initial.pending.map receiptJson)),
      ("initialEntries", entriesJson initialEntries),
      ("codeCatalogue", toJson (codes.map fun entry => obj [
        ("hash", toJson entry.code.hash), ("size", toJson entry.code.size)])),
      ("blocks", toJson trace), ("stop", toJson stop), ("unrunBlocks", toJson unrun),
      ("quiescent", toJson snapshot.quiescent), ("nativeActionRandomness", toJson true)] ++ extra)
  let mut snapshot := initial
  let mut context := context
  let mut trace : List Json := []
  for ((block, hashes), position) in (blocks.zip hashes).zipIdx do
    unless block.txs.length == hashes.length do throw "transaction block-hash count mismatch"
    for hash in hashes do let _ ← NativeIdentity.checkedHash hash
    match block.receipts.resolve snapshot.pending with
    | .error (.unavailableIndex index) =>
      return finish snapshot trace "invalidSchedule" (blocks.length - position - 1) [("unavailableIndex", toJson index)]
    | .ok _ => pure ()
    let inputs := (block.txs.zip hashes).map fun (transaction, blockHash) =>
      ({ transaction, blockHash } : TransactionRegistry.Input)
    let admitted ← TransactionRegistry.observe cfg block.ap catalogue snapshot.state inputs context
    let block := { block with ap := { block.ap with nativeReceiptHashes := some admitted.context.receipts } }
    match step cfg (codeOf codes) snapshot block with
    | .error (.unavailableIndex index) =>
      return finish snapshot trace "invalidSchedule" (blocks.length - position - 1) [("unavailableIndex", toJson index)]
    | .ok (next, result) =>
      if result.issue.isSome then
        trace := trace ++ [obj [("execution", applyJson cfg block.txs next result), ("registry", contextJson context),
          ("identityBirths", birthsJson result.identityBirths),
          ("transactionIdentities", transactionIdentitiesJson admitted.attempts), ("admissionCommitted", toJson false)]]
        return finish next trace "executionIssue" (blocks.length - position - 1)
      context ← ReceiptRegistry.observeQueues cfg catalogue block.ap.blockHeight snapshot.state result admitted.context
      let outgoing ← result.outgoing.mapM (encodeReceipt catalogue context)
      let entries ← QueueEncoding.queues next.state catalogue context (some cfg)
      let stateEntries ← QueueEncoding.encode next.state catalogue context (some cfg)
      trace := trace ++ [obj [("execution", applyJson cfg block.txs next result), ("registry", contextJson context),
        ("identityBirths", birthsJson result.identityBirths), ("outgoingBytes", toJson outgoing),
        ("queueEntries", entriesJson entries), ("stateEntries", entriesJson stateEntries),
        ("transactionIdentities", transactionIdentitiesJson admitted.attempts), ("admissionCommitted", toJson true)]]
      snapshot := next
  return finish snapshot trace "blocksExhausted" 0

def execute (request : Json) : IO Json := do
  let (protocol, directory, catalogues, initial, pending, values, hashes, context) ← IO.ofExcept do
    object request ["formatVersion", "protocolVersion", "configDir", "codes", "initialState", "pendingReceipts",
      "blocks", "transactionBlockHashes", "queueContext"]
    let version : Nat ← field request "formatVersion"
    unless version == 1 do throw "unsupported formatVersion"
    let protocol : Nat ← field request "protocolVersion"
    unless 83 ≤ protocol && protocol ≤ 86 do throw "reference protocol range is 83–86"
    let context : Option Json ← fromJson? ((request.getObjVal? "queueContext").toOption.getD .null)
    pure (protocol, ← field request "configDir", ← field request "codes", ← field request "initialState",
      ← field request "pendingReceipts", ← field request "blocks", ← field request "transactionBlockHashes", context)
  let codes ← loadCatalogue (catalogues : List Json)
  let (snapshot, blocks, hashes, context) ← IO.ofExcept do
    let snapshot : Snapshot := {
      state := ← state codes initial
      pending := ← (pending : List Json).mapM (receipt codes) }
    let blocks ← (values : List Json).mapM (block codes)
    let hashes ← (hashes : List (List (List Nat))).mapM (List.mapM bytes)
    let context ← match context with
      | none => pure ({} : QueueEncoding.Context)
      | some context => QueueContext.parse context
    pure (snapshot, blocks, hashes, context)
  let cfg ← Wasm.Near.RuntimeConfig.load directory protocol
  IO.ofExcept (run protocol cfg codes snapshot context blocks hashes)

end ChainReplay.Registered

def main : IO Unit := do
  let request ← IO.ofExcept (Lean.Json.parse (← (← IO.getStdin).readToEnd))
  IO.println (← ChainReplay.Registered.execute request).compress
