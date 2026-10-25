import NearRuntime.Apply
import NearRuntime.QueueEncoding

/-! Register receipt/data births emitted by the actual runtime transition.
Native generated hashes are never inputs: parent bindings, execution height,
original action positions and final child order determine the new identities.
Queue pops/appends preserve persistent indices and freeze newly stored metadata. -/
namespace Near.ReceiptRegistry

open EncodingPrimitives

private def register (height : Nat) (context : QueueEncoding.Context)
    (birth : ReceiptIdentityBirth) : Except String QueueEncoding.Context := do
  let parent ← match birth.parentHash with
    | some hash => NativeIdentity.checkedHash hash
    | none => NativeIdentity.resolve context.receipts birth.parent
  unique "child identity" birth.children
  unique "VM action position" (birth.vmActions.map (·.actionIndex))
  let vmReceipts := birth.vmActions.flatMap (·.receipts)
  unique "VM receipt identity" vmReceipts
  for id in vmReceipts do
    unless birth.children.contains id do throw "VM receipt is absent from final child order"
  let mut next := context
  for (id, index) in birth.children.zipIdx do
    if next.receipts.any (·.1 == id) || next.formats.any (·.1 == id) || next.data.any (·.id == id) then
      throw "child logical identity is already registered"
    let hash ← NativeIdentity.receipt parent height (birth.startIndex + index)
    next := { next with
      receipts := next.receipts ++ [(id, hash)]
      formats := next.formats ++ [(id, if vmReceipts.contains id then .v2 else .legacy)] }
  for action in birth.vmActions do
    let actionHash ← NativeIdentity.action parent height action.actionIndex
    for (((id, receiver), position), nth) in (action.data.zipIdx).zipIdx do
      let index := if action.dataIndices.isEmpty then position else action.dataIndices.getD nth position
      if next.data.any (·.id == id) || next.receipts.any (·.1 == id) then
        throw "data logical identity is already registered"
      unless Wasm.Near.validAccountIdBytes receiver.toUTF8.toList do throw "invalid data receiver"
      let hash ← NativeIdentity.data actionHash height index
      next := { next with data := next.data ++ [{ id, hash, receiver }] }
  NativeIdentity.validate next.receipts
  NativeIdentity.validate (next.data.map fun data => (data.id, data.hash))
  return next

/-- A model issue invalidates the chunk, including its identity observations.
Transaction receipt bindings must already come from original typed bodies.
Data receipts which awaken postponed actions retain those actions' parent IDs. -/
def observe (height : Nat) (result : ApplyResult) (context : QueueEncoding.Context) :
    Except String QueueEncoding.Context := do
  if result.issue.isSome then throw "cannot register an unsupported apply"
  let mut next := context
  for birth in result.identityBirths do
    next ← register height next birth
  return next

/-- Advance persisted queue context from the actual pop/append counts. New
stored metadata is frozen at birth, so later configuration changes cannot
rewrite a receipt's original gas/size wrapper. The old context is checked
against the pre-state, and the complete new queue encoding is checked before
publishing the extended context. -/
def observeQueues (cfg : Wasm.Near.RuntimeConfig) (codes : List (String × Bytes))
    (height : Nat) (before : ChainState) (result : ApplyResult) (context : QueueEncoding.Context) :
    Except String QueueEncoding.Context := do
  let _ ← QueueEncoding.queues before codes context (some cfg)
  let next ← observe height result context
  let oldForms := context.delayed.map (·.forms) |>.getD []
  unless result.delayedConsumed ≤ oldForms.length do throw "delayed queue consumed beyond its old end"
  let retained := oldForms.drop result.delayedConsumed
  unless result.state.delayed.length == retained.length + result.delayedAppended do
    throw "delayed queue transition length mismatch"
  let appended ← (result.state.delayed.drop retained.length).mapM fun receipt => do
    let encoded ← QueueEncoding.receiptBytes next codes receipt
    pure (QueueEncoding.StorageForm.storedV1 (QueueEncoding.congestionGas cfg receipt) encoded.length)
  let firstIndex := (context.delayed.map (·.firstIndex)).getD 0 + result.delayedConsumed
  let delayed := if context.delayed.isSome || result.delayedAppended > 0 then
    some ({ firstIndex, forms := retained ++ appended } : QueueEncoding.Delayed) else none
  let next := { next with delayed }
  let _ ← QueueEncoding.queues result.state codes next (some cfg)
  return next

/-- Failed action receipts cannot publish successful VM allocation origins. -/
theorem rollback_discards_vm_births (state : ChainState) (exec : Exec) (error : RuntimeError) :
    (rollbackReceipt state exec (some error)).vmIdentityBirths = [] := rfl

/-- Model issues expose no chunk identity births, just as they expose no funds
or receipt transitions. -/
theorem apply_issue_discards_births (cfg : Wasm.Near.RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (state : ChainState) (transactions : List Transaction)
    (incoming : List Receipt) (h : (apply cfg ap decoder state transactions incoming).issue.isSome = true) :
    (apply cfg ap decoder state transactions incoming).identityBirths = [] := by
  unfold apply at h ⊢
  dsimp only at h ⊢
  split <;> simp_all

end Near.ReceiptRegistry
