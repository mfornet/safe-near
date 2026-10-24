import NearRuntime.Apply
import NearInterface.Refines
import NearVM.Fuel
import NearVM.StorageListing

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
  have houtputs' : (if isLast then c.action.outputDataReceivers.map fun d => bytesOfString d.receiverId
      else []) = ctx.outputDataReceivers.map NearInterface.AccountId.bytes := by
    have hbytes : ctx.outputDataReceivers.map NearInterface.AccountId.bytes =
        (ctx.outputDataReceivers.map Subtype.val).map bytesOfString := by
      simp [NearInterface.AccountId.bytes, bytesOfString]
    rw [hbytes, houtputs]
    split <;> simp [List.map_map, Function.comp_def]
  unfold functionCallContext
  rw [houtputs']
  simp only [toVMContext, NearInterface.AccountId.bytes, bytesOfString, hcurrent, hsigner, hpk,
    hpredecessor, hargs, hresults, hheight, htime, hepoch, hbalance, hlocked, husage, hdeposit, hgas,
    hseed, htrie]

/-- What the boundary runs: the deployed code, and the decoder the runtime
uses for code that the call's promises deploy. -/
structure Code where
  code : ContractCode
  codeOf : Bytes → ContractCode

/-- Why the runtime cannot convert a promised action, if it cannot. -/
def actionIssue? (codeOf : Bytes → ContractCode) (action : PromiseAction) : Option ExecutionIssue :=
  match actionOfPromise codeOf action with
  | .error (.executionIssue issue) => some issue
  | .error error => some (.interpreterError (repr error).pretty)
  | .ok _ => none

/-- The first promised action the runtime cannot convert
(`validateFunctionCallActions`). -/
def actionsIssue? (codeOf : Bytes → ContractCode) (receipts : List ReceiptSpec) :
    Option ExecutionIssue :=
  receipts.findSome? fun spec => spec.actions.findSome? (actionIssue? codeOf)

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
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError := none) : Observation :=
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
    match receiptError with
    | some error => failed (.other (repr error).pretty)
    | none =>
      let deficit := stakeDeficit ctx.protocol outcome.storageUsage outcome.balance ctx.locked
      if deficit > 0 then failed (.lackBalanceForState deficit)
      else
        { outcome := .ok outcome.returnData, storage := outcome.storage.toFinset,
          balance := outcome.balance, storageUsage := outcome.storageUsage,
          burntGas := outcome.burntGas, usedGas := outcome.usedGas - outcome.distributedGas,
          logs := outcome.logs,
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
      (match checkVMReceipts ctx.protocol code.codeOf ctx.current ctx.signer ctx.signerPk outcome.receipts with
       | .error error => some (.newReceiptValidationError error)
       | .ok () => none)

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
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError) {failure : Failure}
    (h : (observe ctx storage outcome issue receiptError).outcome = .error failure) :
    NearInterface.RolledBack ctx storage.toFinset (observe ctx storage outcome issue receiptError) := by
  revert h
  unfold observe
  split
  · intro _; exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
  · split
    · intro _; exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
    · split
      · intro _; exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
      · dsimp only
        split
        · intro _; exact ⟨⟨_, rfl⟩, rfl, rfl, rfl, rfl⟩
        · intro h; cases h

theorem execOn_rolledBack (code : Code) (storage : List (Bytes × Bytes)) (ctx : Context)
    {failure : Failure} (h : (execOn code storage ctx).outcome = .error failure) :
    NearInterface.RolledBack ctx storage.toFinset (execOn code storage ctx) := by
  revert h
  unfold execOn
  cases code.code.decodeIssue <;> dsimp only <;> exact observe_rolledBack _ _ _ _ _

/-- Every failed execution of the instance leaves the account as it was. -/
theorem nearRuntime_failure_rolledBack (code : Code) (raw : RawStorage) (ctx : Context)
    {failure : Failure} (h : (nearRuntime.exec code raw ctx).outcome = .error failure) :
    NearInterface.RolledBack ctx raw (nearRuntime.exec code raw ctx) := by
  have := execOn_rolledBack code raw.toList ctx h
  simpa [nearRuntime, Finset.toList_toFinset] using this

/-! ## Fuel

The VM call uses `run`'s default fuel, `fuelFor`, as `applyFunctionCall` does.
Under the runtime's guarantees it is enough: more fuel never changes the
outcome, so no execution stops for want of interpreter steps. -/

theorem execOn_fuel_independent (code : Code) (storage : List (Bytes × Bytes)) {ctx : Context}
    {raw : RawStorage} (hwf : ctx.WF raw) (n : Nat) :
    run ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx) storage
        (fuelFor ctx.protocol code.code.module (toVMContext ctx) + n) =
      run ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx) storage :=
  run_fuel_independent _ _ _ _ _ _ (Nat.lt_min.mpr hwf.opCost_pos) n

/-! ## Storage listing

The VM reads storage from a list; `RawStorage` is a set. Two listings of the
same records give the same observation, so `nearRuntime` depends on the
storage only as a set. -/

theorem observe_echo (ctx : Context) {s₁ s₂ : List (Bytes × Bytes)} (hs : s₁.toFinset = s₂.toFinset)
    {o₁ o₂ : VMOutcome} (h : EchoRel o₁ o₂) (issue : Option ExecutionIssue)
    (receiptError : Option RuntimeError := none) :
    observe ctx s₁ o₁ issue receiptError = observe ctx s₂ o₂ issue receiptError := by
  obtain ⟨hf, hst⟩ := h
  have field {β : Type} (f : VMOutcome → β) (hf' : ∀ o : VMOutcome, f { o with storage := [] } = f o) :
      f o₁ = f o₂ := by
    rw [← hf' o₁, ← hf' o₂, hf]
  have ha : o₁.aborted = o₂.aborted := field VMOutcome.aborted fun _ => rfl
  have hacc : o₁.storageAccounting = o₂.storageAccounting := field VMOutcome.storageAccounting fun _ => rfl
  have hb : o₁.burntGas = o₂.burntGas := field VMOutcome.burntGas fun _ => rfl
  have hu : o₁.usedGas = o₂.usedGas := field VMOutcome.usedGas fun _ => rfl
  have hl : o₁.logs = o₂.logs := field VMOutcome.logs fun _ => rfl
  have hr : o₁.returnData = o₂.returnData := field VMOutcome.returnData fun _ => rfl
  have hbal : o₁.balance = o₂.balance := field VMOutcome.balance fun _ => rfl
  have husage : o₁.storageUsage = o₂.storageUsage := field VMOutcome.storageUsage fun _ => rfl
  have hrec : o₁.receipts = o₂.receipts := field VMOutcome.receipts fun _ => rfl
  have hd : o₁.distributedGas = o₂.distributedGas := field VMOutcome.distributedGas fun _ => rfl
  unfold observe
  rw [hs, ha, hacc, hb, hu, hl, hr, hbal, husage, hrec, hd]
  cases hab : o₂.aborted with
  | some e => rfl
  | none => rw [hst (ha.trans hab)]

/-- The boundary does not depend on how the storage is listed. -/
theorem execOn_perm (code : Code) {s₁ s₂ : List (Bytes × Bytes)} (h : s₁.Perm s₂)
    (hu : KeysUnique s₁) (ctx : Context) : execOn code s₁ ctx = execOn code s₂ ctx := by
  have hs : s₁.toFinset = s₂.toFinset := List.toFinset_eq_of_perm _ _ h
  unfold execOn
  split
  · exact observe_echo ctx hs (failedBefore_echo _ _ _ _ _ _) none
  · have hrun := run_perm ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx) h hu
      (fuelFor ctx.protocol code.code.module (toVMContext ctx))
    have hrec : (run ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx) s₁).receipts =
        (run ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx) s₂).receipts := by
      have := congrArg VMOutcome.receipts hrun.1
      simpa using this
    dsimp only
    rw [hrec]
    exact observe_echo ctx hs hrun _ _

/-- `nearRuntime` computes, on any listing of the storage, what the boundary
computes on that listing. -/
theorem nearRuntime_exec_listing (code : Code) {raw : RawStorage} {ctx : Context}
    (hwf : ctx.WF raw) {l : List (Bytes × Bytes)} (hl : l.toFinset = raw) (hnd : l.Nodup) :
    nearRuntime.exec code raw ctx = execOn code l ctx := by
  show execOn code raw.toList ctx = execOn code l ctx
  apply execOn_perm code _ _ ctx
  · rw [← hl]; exact List.toFinset_toList hnd
  · intro k v v' hv hv'
    exact hwf.raw_keys_unique k v v' (Finset.mem_toList.mp hv) (Finset.mem_toList.mp hv')

end Near.Boundary
