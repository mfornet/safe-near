import NearRuntime.Apply
import NearInterface.Refines

/-!
# near-lean as a `RuntimeInterface`

The function-call action boundary of `NearInterface`, instantiated by this
runtime: the VM run that `applyFunctionCall` performs, followed by the
receipt's `checkStorageStake`, as the receipt executor runs a receipt whose
only action is that call. The receipt's own fees (`new_action_receipt`,
the function-call action fee) are charged outside the boundary.

The seam with the receipt executor is stated, not duplicated:

* `functionCallContext_eq_toVMContext`: the VM context `applyFunctionCall`
  builds is `Context.toVMContext` of the corresponding boundary context.
* `storageStakeDeficit` (`Apply.lean`) is `NearInterface.stakeDeficit`.
* `execOn` calls the same `run`, with the same fuel, and validates the
  promised actions as `validateFunctionCallActions` does.

All projection from `VMOutcome` to `Observation` happens here, so the
interface sees no `Option` fields and no fallbacks.
-/

namespace Near.Boundary

open Wasm Wasm.Near
open NearInterface (Context Failure Observation RuntimeInterface RawStorage stakeDeficit)

/-- The VM context of a function-call action, with the receipt executor's
policies (`functionCallContext`): UTF-8 method validation, charged
storage-value access, accounting against the chunk trie. -/
def toVMContext (ctx : Context) : VMContext where
  validateActionMethodUtf8 := true
  currentAccountId := ctx.current.bytes
  signerAccountId := ctx.signer.bytes
  signerAccountPk := ctx.signerPk
  predecessorAccountId := ctx.predecessor.bytes
  input := ctx.args
  promiseResults := ctx.promiseResults
  blockHeight := ctx.blockHeight
  blockTimestamp := ctx.timestamp
  epochHeight := ctx.epochHeight
  accountBalance := ctx.balance
  accountLockedBalance := ctx.locked
  storageUsage := ctx.storageUsage
  attachedDeposit := ctx.attached
  prepaidGas := ctx.prepaidGas
  randomSeed := ctx.randomSeed
  storageAccounting := some ctx.trie
  chargeStorageValueAccess := true
  outputDataReceivers := ctx.outputDataReceivers.map NearInterface.AccountId.bytes

/-- The receipt executor builds exactly `toVMContext` from a context that
agrees with the receipt, the account and the action. -/
theorem functionCallContext_eq_toVMContext (c : ReceiptCtx) (account : Account) (args : Bytes)
    (gas deposit : Nat) (isLast : Bool) (trie : TrieOverlay.State) (ctx : Context)
    (hcurrent : ctx.current.val = c.receipt.receiverId)
    (hsigner : ctx.signer.val = c.action.signerId)
    (hpk : ctx.signerPk = c.action.signerPublicKey)
    (hpredecessor : ctx.predecessor.val = c.receipt.predecessorId)
    (hargs : ctx.args = args) (hresults : ctx.promiseResults = c.promiseResults)
    (hheight : ctx.blockHeight = c.ap.blockHeight) (htime : ctx.timestamp = c.ap.blockTimestamp)
    (hepoch : ctx.epochHeight = c.ap.epochHeight)
    (hbalance : ctx.balance = account.amount) (hlocked : ctx.locked = account.locked)
    (husage : ctx.storageUsage = account.storageUsage)
    (hdeposit : ctx.attached = deposit) (hgas : ctx.prepaidGas = gas)
    (hseed : ctx.randomSeed = c.vmRandomSeed.getD c.ap.randomSeed) (htrie : ctx.trie = trie)
    (houtputs : ctx.outputDataReceivers.map Subtype.val =
      if isLast then c.action.outputDataReceivers.map (·.receiverId) else []) :
    functionCallContext c account args gas deposit isLast (some trie) = toVMContext ctx := by
  have houtputs' : ctx.outputDataReceivers.map NearInterface.AccountId.bytes =
      if isLast then c.action.outputDataReceivers.map fun d => bytesOfString d.receiverId else [] := by
    have := congrArg (List.map bytesOfString) houtputs
    split at this <;> simpa [List.map_map, Function.comp_def, NearInterface.AccountId.bytes,
      bytesOfString] using this
  simp only [functionCallContext, toVMContext, NearInterface.AccountId.bytes, bytesOfString,
    hcurrent, hsigner, hpk, hpredecessor, hargs, hresults, hheight, htime, hepoch, hbalance,
    hlocked, husage, hdeposit, hgas, hseed, htrie]
  rw [← houtputs']
  rfl

/-- What the boundary runs: the deployed code, and the decoder the runtime
uses for code that the call's promises deploy. -/
structure Code where
  code : ContractCode
  codeOf : Bytes → ContractCode

/-- The first promised action the runtime cannot convert
(`validateFunctionCallActions`). -/
def actionsIssue? (codeOf : Bytes → ContractCode) (receipts : List ReceiptSpec) :
    Option ExecutionIssue :=
  receipts.findSome? fun spec => spec.actions.findSome? fun action =>
    match actionOfPromise codeOf action with
    | .error (.executionIssue issue) => some issue
    | .error error => some (.interpreterError (repr error).pretty)
    | .ok _ => none

/-- The failure a VM error reports at the boundary. -/
def failureOf (error : FunctionCallError) : Failure :=
  match error.issue? with
  | some issue => .executionIssue issue.message
  | none =>
    match error with
    | .hostError (.guestPanic msg) => .panic msg
    | .hostError .gasExceeded | .hostError .gasLimitExceeded => .outOfGas
    | .hostError .balanceExceeded => .balanceExceeded
    | .methodResolveError .methodNotFound => .methodNotFound
    | error => .other error.message

/-- Project a VM outcome onto the boundary, applying the storage-stake check
to the post-state. A failure, the VM's or the stake check's, rolls back
storage, balance, usage, receipts and the trie's prospective writes, and
keeps burnt gas, logs and cache warming (`rollbackReceipt`). -/
def observe (ctx : Context) (storage : List (Bytes × Bytes)) (outcome : VMOutcome)
    (issue : Option ExecutionIssue) : Observation :=
  let trie := outcome.storageAccounting.getD ctx.trie
  let failed (failure : Failure) : Observation :=
    { outcome := .error failure, storage := storage.toFinset, balance := ctx.balance,
      storageUsage := ctx.storageUsage, burntGas := outcome.burntGas,
      usedGas := outcome.burntGas, logs := outcome.logs, receipts := [],
      trie := { trie with prospective := [] } }
  match outcome.aborted with
  | some error => failed (failureOf error)
  | none =>
    match issue with
    | some issue => failed (.executionIssue issue.message)
    | none =>
      let deficit := stakeDeficit ctx.protocol outcome.storageUsage outcome.balance ctx.locked
      if deficit > 0 then failed (.lackBalanceForState deficit)
      else
        { outcome := .ok outcome.returnData, storage := outcome.storage.toFinset,
          balance := outcome.balance, storageUsage := outcome.storageUsage,
          burntGas := outcome.burntGas, usedGas := outcome.usedGas, logs := outcome.logs,
          receipts := outcome.receipts, trie }

/-- The boundary on one listing of the contract storage. Same VM call and
fuel as `applyFunctionCall`. -/
def execOn (code : Code) (storage : List (Bytes × Bytes)) (ctx : Context) : Observation :=
  match code.code.decodeIssue with
  | some issue =>
    observe ctx storage (VMOutcome.failedBefore (toVMContext ctx) storage 0 (.executionIssue issue))
      none
  | none =>
    let outcome := run ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx)
      storage
    observe ctx storage outcome (actionsIssue? code.codeOf outcome.receipts)

/-- near-lean, seen through one function-call action. The VM reads storage
from a list; `RawStorage` is a set, so the instance picks a listing. That the
observation does not depend on which listing is a proof obligation
(`notes/todo/refinement_equivalence.md`, section 9). -/
noncomputable def nearRuntime : RuntimeInterface where
  Code := Code
  exec code raw ctx := execOn code raw.toList ctx

/-! ## Total observations -/

/-- Every failure rolls back storage, balance, usage and receipts. -/
theorem observe_rolledBack (ctx : Context) (storage : List (Bytes × Bytes)) (outcome : VMOutcome)
    (issue : Option ExecutionIssue) {failure : Failure}
    (h : (observe ctx storage outcome issue).outcome = .error failure) :
    NearInterface.RolledBack ctx storage.toFinset (observe ctx storage outcome issue) := by
  unfold observe at h ⊢
  split
  · exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
      · rename_i hab _ _
        simp only [hab] at h
        split at h <;> simp_all

theorem execOn_rolledBack (code : Code) (storage : List (Bytes × Bytes)) (ctx : Context)
    {failure : Failure} (h : (execOn code storage ctx).outcome = .error failure) :
    NearInterface.RolledBack ctx storage.toFinset (execOn code storage ctx) := by
  unfold execOn at h ⊢
  split
  · rename_i hissue
    simp only [hissue] at h
    exact observe_rolledBack _ _ _ _ h
  · rename_i hissue
    simp only [hissue] at h
    exact observe_rolledBack _ _ _ _ h

/-- Every failed execution of the instance leaves the account as it was. -/
theorem nearRuntime_failure_rolledBack (code : Code) (raw : RawStorage) (ctx : Context)
    {failure : Failure} (h : (nearRuntime.exec code raw ctx).outcome = .error failure) :
    NearInterface.RolledBack ctx raw (nearRuntime.exec code raw ctx) := by
  have := execOn_rolledBack code raw.toList ctx h
  simpa [nearRuntime, Finset.toList_toFinset] using this

end Near.Boundary
