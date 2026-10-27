import NearRuntime.BoundaryResolution

/-!
# From exported-function contracts to refinement

The VM postconditions mention VM fields and boundary checks, letting a
function proof use `observe` without unfolding it. Assembly supplies rollback
and asks for the low-gas alternative only below the model's bound.

Gas-budget monotonicity is not asserted here. The low-gas contract must still
prove matching or out-of-gas with a prefix of the model's logs.
-/

namespace Near.Boundary
open Wasm Wasm.Near NearInterface

/-- Successful VM fields and all checks required before committing effects. -/
structure SuccessPost (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (o : VMOutcome) (issue : Option ExecutionIssue) (receiptError : Option RuntimeError)
    (result : Outcome M.State M.Ret M.Promise) : Prop where
  aborted : o.aborted = none
  actions : issue = none
  receiptsValid : receiptError = none
  stake : stakeDeficit ctx.protocol o.storageUsage o.balance ctx.locked = 0
  returned : o.returnData = M.encodeRet result.ret
  storage : o.storage.toFinset = M.encodeState result.state
  balance : o.balance = ctx.balance + ctx.attached -
    receiptDeposits (M.encodeReceipts (ctx.prepaidGas - (o.usedGas - o.distributedGas)) result.promises)
  usage : o.storageUsage = ctx.storageUsage - storageUsageOf ctx.protocol raw +
    storageUsageOf ctx.protocol (M.encodeState result.state)
  logs : o.logs = result.logs
  receipts : o.receipts =
    M.encodeReceipts (ctx.prepaidGas - (o.usedGas - o.distributedGas)) result.promises

/-- A function's abort and logs; the boundary supplies account rollback. -/
def AbortPost (M : ContractModel) (o : VMOutcome) (result : Failed M.Panic) : Prop :=
  ∃ error, o.aborted = some error ∧
    failureOf error = ContractModel.ModelFailure.toFailure M result.failure ∧ o.logs = result.logs

theorem observe_matches_success {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : Outcome M.State M.Ret M.Promise}
    (h : SuccessPost M ctx storage.toFinset o issue receiptError result) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError) (.ok result) := by
  simp only [observe, h.aborted, h.actions, h.receiptsValid, h.stake, Nat.lt_irrefl,
    ↓reduceIte, Matches]
  exact ⟨congrArg Except.ok h.returned, h.storage, h.balance, h.usage, h.logs, h.receipts⟩

theorem observe_matches_abort {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : Failed M.Panic}
    (h : AbortPost M o result) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError) (.error result) := by
  obtain ⟨error, habort, hfailure, hlogs⟩ := h
  simp [observe, habort, Matches, hfailure, hlogs]

/-- Raw evidence for each failure exit of `observe`, in its actual check
order. Each constructor records the earlier checks that must have passed;
there is no assumption about the already projected observation. -/
inductive FailurePost (ctx : Context) (o : VMOutcome) (issue : Option ExecutionIssue)
    (receiptError : Option RuntimeError) : Failure → Prop
  | aborted (error : FunctionCallError) (habort : o.aborted = some error) :
      FailurePost ctx o issue receiptError (failureOf error)
  | actions (error : ExecutionIssue) (habort : o.aborted = none)
      (hactions : issue = some error) :
      FailurePost ctx o issue receiptError (.executionIssue error.message)
  | receipts (error : RuntimeError) (habort : o.aborted = none)
      (hactions : issue = none) (hreceipts : receiptError = some error) :
      FailurePost ctx o issue receiptError (runtimeFailure error)
  | stake (habort : o.aborted = none) (hactions : issue = none)
      (hreceipts : receiptError = none)
      (hdeficit : 0 < stakeDeficit ctx.protocol o.storageUsage o.balance ctx.locked) :
      FailurePost ctx o issue receiptError
        (.lackBalanceForState (stakeDeficit ctx.protocol o.storageUsage o.balance ctx.locked))

/-- All boundary failures expose the irreversible burn, including failures
that happen after the VM returns successfully. -/
theorem observe_failure_of_post {ctx : Context} {storage : List (Bytes × Bytes)}
    {o : VMOutcome} {issue : Option ExecutionIssue} {receiptError : Option RuntimeError}
    {failure : Failure} (h : FailurePost ctx o issue receiptError failure) :
    (observe ctx storage o issue receiptError).outcome = .error failure ∧
      (observe ctx storage o issue receiptError).usedGas = o.burntGas ∧
      (observe ctx storage o issue receiptError).logs = o.logs := by
  cases h with
  | aborted error habort => simp [observe, habort]
  | actions error habort hactions => simp [observe, habort, hactions]
  | receipts error habort hactions hreceipts => simp [observe, habort, hactions, hreceipts]
  | stake habort hactions hreceipts hdeficit =>
      simp [observe, habort, hactions, hreceipts, hdeficit]

/-- Matching a model failure needs its failure and logs; the boundary supplies
all the restored account fields. -/
theorem observe_matches_failure {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : Failed M.Panic}
    (h : FailurePost ctx o issue receiptError (ContractModel.ModelFailure.toFailure M result.failure))
    (hlogs : o.logs = result.logs) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError) (.error result) := by
  obtain ⟨hout, _, hlog⟩ := observe_failure_of_post (storage := storage) h
  obtain ⟨_, hstorage, hbalance, husage, hreceipts⟩ := observe_rolledBack _ _ _ _ _ hout
  exact ⟨hout, hstorage, hbalance, husage, hlog.trans hlogs, hreceipts⟩

/-- Storage stake failure is checked after the VM and both receipt checks;
it is a model failure even though the VM itself returned successfully. -/
theorem observe_matches_stakeFailure {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {logs : List String}
    (habort : o.aborted = none) (hactions : issue = none) (hreceipts : receiptError = none)
    (hdeficit : 0 < stakeDeficit ctx.protocol o.storageUsage o.balance ctx.locked)
    (hlogs : o.logs = logs) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError)
      (.error ⟨.lackBalanceForState
        (stakeDeficit ctx.protocol o.storageUsage o.balance ctx.locked), logs⟩) :=
  observe_matches_failure (.stake habort hactions hreceipts hdeficit) hlogs

/-- A receipt rejected by runtime validation reports its formatted validation
message and rolls back. It takes precedence over the storage-stake check. -/
theorem observe_matches_receiptFailure {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {logs : List String} (error : ReceiptValidationError)
    (habort : o.aborted = none) (hactions : issue = none)
    (hreceipts : receiptError = some (.newReceiptValidationError error)) (hlogs : o.logs = logs) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError)
      (.error ⟨.receiptInvalid (ReceiptValidation.newReceiptInvalid error.message), logs⟩) :=
  observe_matches_failure (.receipts (.newReceiptValidationError error) habort hactions hreceipts) hlogs

/-- Raw VM and boundary-check evidence for a model step, covering every
success or failure exit of `observe`. -/
def VMPost (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (o : VMOutcome) (issue : Option ExecutionIssue) (receiptError : Option RuntimeError) :
    StepResult M.Panic M.State M.Ret M.Promise → Prop
  | .ok result => SuccessPost M ctx raw o issue receiptError result
  | .error result =>
      FailurePost ctx o issue receiptError (ContractModel.ModelFailure.toFailure M result.failure) ∧
        o.logs = result.logs

/-- Existing VM-abort contracts also satisfy the general failure postcondition. -/
theorem AbortPost.to_vmPost {M : ContractModel} {ctx : Context} {raw : RawStorage}
    {o : VMOutcome} {issue : Option ExecutionIssue} {receiptError : Option RuntimeError}
    {result : Failed M.Panic} (h : AbortPost M o result) :
    VMPost M ctx raw o issue receiptError (.error result) := by
  obtain ⟨error, habort, hfailure, hlogs⟩ := h
  exact ⟨hfailure ▸ FailurePost.aborted error habort, hlogs⟩

/-- Adequacy of a raw VM postcondition for boundary observation. -/
theorem observe_matches_of_post {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : StepResult M.Panic M.State M.Ret M.Promise}
    (h : VMPost M ctx storage.toFinset o issue receiptError result) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError) result := by
  cases result with
  | ok result => exact observe_matches_success h
  | error result => exact observe_matches_failure h.1 h.2

/-- The gas seen by the interface on a committed return excludes distributed
gas. This is the quantity a successful function contract must bound. -/
theorem observe_usedGas_success {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : Outcome M.State M.Ret M.Promise}
    (h : SuccessPost M ctx storage.toFinset o issue receiptError result) :
    (observe ctx storage o issue receiptError).usedGas = o.usedGas - o.distributedGas := by
  simp only [observe, h.aborted, h.actions, h.receiptsValid, h.stake, Nat.lt_irrefl, ↓reduceIte]

/-- An abort discards promised gas and exposes only the irreversible burn. -/
theorem observe_usedGas_abort {ctx : Context} {storage : List (Bytes × Bytes)}
    {o : VMOutcome} {issue : Option ExecutionIssue} {receiptError : Option RuntimeError}
    {error : FunctionCallError} (h : o.aborted = some error) :
    (observe ctx storage o issue receiptError).usedGas = o.burntGas := by
  simp only [observe, h]

/-- A model-shaped raw postcondition determines which gas quantity is
observable, even when failure happens after a successful VM return. -/
theorem observe_usedGas_of_post {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : StepResult M.Panic M.State M.Ret M.Promise}
    (h : VMPost M ctx storage.toFinset o issue receiptError result) :
    (observe ctx storage o issue receiptError).usedGas =
      match result with
      | .ok _ => o.usedGas - o.distributedGas
      | .error _ => o.burntGas := by
  cases result with
  | ok result => exact observe_usedGas_success h
  | error result => exact (observe_failure_of_post h.1).2.1

/-- Function contracts establish a raw postcondition and the gas quantity
appropriate to their result; this gives both sufficient-gas refinement goals. -/
theorem observe_adequacy {M : ContractModel} {ctx : Context}
    {storage : List (Bytes × Bytes)} {o : VMOutcome} {issue : Option ExecutionIssue}
    {receiptError : Option RuntimeError} {result : StepResult M.Panic M.State M.Ret M.Promise}
    {bound : Gas} (h : VMPost M ctx storage.toFinset o issue receiptError result)
    (hgas : (match result with
      | .ok _ => o.usedGas - o.distributedGas
      | .error _ => o.burntGas) ≤ bound) :
    Matches M ctx storage.toFinset (observe ctx storage o issue receiptError) result ∧
      (observe ctx storage o issue receiptError).usedGas ≤ bound :=
  ⟨observe_matches_of_post h, (observe_usedGas_of_post h) ▸ hgas⟩

/-- Without invariants on a raw `VMOutcome`, these are the two possible
observed gas quantities, so their maximum bounds every exit. -/
theorem observe_usedGas_le_max (ctx : Context) (storage : List (Bytes × Bytes))
    (o : VMOutcome) (issue : Option ExecutionIssue) (receiptError : Option RuntimeError) :
    (observe ctx storage o issue receiptError).usedGas ≤
      max o.burntGas (o.usedGas - o.distributedGas) := by
  unfold observe
  split
  · exact Nat.le_max_left _ _
  · split
    · exact Nat.le_max_left _ _
    · split
      · exact Nat.le_max_left _ _
      · dsimp only
        split
        · exact Nat.le_max_left _ _
        · exact Nat.le_max_right _ _

/-- For a gas-bounded VM result, projecting any boundary exit never increases
the VM's used gas. This includes rollback after receipt or stake validation. -/
theorem observe_usedGas_le (ctx : Context) (storage : List (Bytes × Bytes))
    (o : VMOutcome) (issue : Option ExecutionIssue) (receiptError : Option RuntimeError)
    (hgas : o.burntGas ≤ o.usedGas) :
    (observe ctx storage o issue receiptError).usedGas ≤ o.usedGas :=
  (observe_usedGas_le_max ctx storage o issue receiptError).trans
    (max_le hgas (Nat.sub_le _ _))

/-- A raw out-of-gas abort gives the low-gas observation, including rollback. -/
theorem observe_outOfGas {ctx : Context} {storage : List (Bytes × Bytes)}
    {o : VMOutcome} {issue : Option ExecutionIssue} {receiptError : Option RuntimeError}
    {logs : List String} {error : FunctionCallError}
    (habort : o.aborted = some error) (hgas : failureOf error = .outOfGas)
    (hlogs : o.logs <+: logs) :
    (observe ctx storage o issue receiptError).outcome = .error .outOfGas ∧
      RolledBack ctx storage.toFinset (observe ctx storage o issue receiptError) ∧
      (observe ctx storage o issue receiptError).logs <+: logs := by
  have hout : (observe ctx storage o issue receiptError).outcome = .error .outOfGas := by
    simp only [observe, habort, hgas]
  exact ⟨hout, observe_rolledBack _ _ _ _ _ hout, by simpa only [observe, habort] using hlogs⟩

/-- Assemble function contracts. Invalid inputs only need a failure witness;
the boundary restores their effects. Low-gas reasoning is needed only below
the bound, independently of the sufficient-gas function proof. -/
theorem refines_of_contracts (code : Code) (protocol : RuntimeConfig) (M : ContractModel)
    (hissue : ∀ raw st ctx, M.Represents raw st → ctx.WF raw → ctx.protocol = protocol →
      ∀ msg, (nearRuntime.exec code raw ctx).outcome ≠ .error (.executionIssue msg))
    (henough : ∀ raw st ctx, M.Represents raw st → ctx.WF raw → ctx.protocol = protocol →
      ∀ c, M.Parses ctx.method ctx.args c → M.gas ctx st c ≤ ctx.gasLimit →
      Matches M ctx raw (nearRuntime.exec code raw ctx) (M.step ctx st c) ∧
        (nearRuntime.exec code raw ctx).usedGas ≤ M.gas ctx st c)
    (hsmall : ∀ raw st ctx, M.Represents raw st → ctx.WF raw → ctx.protocol = protocol →
      ∀ c, M.Parses ctx.method ctx.args c → ctx.gasLimit < M.gas ctx st c →
      Matches M ctx raw (nearRuntime.exec code raw ctx) (M.step ctx st c) ∨
        ((nearRuntime.exec code raw ctx).outcome = .error .outOfGas ∧
          (nearRuntime.exec code raw ctx).logs <+: (M.step ctx st c).logs))
    (hinvalid : ∀ raw st ctx, M.Represents raw st → ctx.WF raw → ctx.protocol = protocol →
      (¬ ∃ c, M.Parses ctx.method ctx.args c) →
      ∃ failure, (nearRuntime.exec code raw ctx).outcome = .error failure) :
    Refines nearRuntime protocol code M := by
  intro raw st ctx hrep hwf hprot
  refine ⟨hissue raw st ctx hrep hwf hprot, ?_, ?_⟩
  · intro c hparse
    refine ⟨henough raw st ctx hrep hwf hprot c hparse, ?_⟩
    by_cases hgas : M.gas ctx st c ≤ ctx.gasLimit
    · exact Or.inl (henough raw st ctx hrep hwf hprot c hparse hgas).1
    · rcases hsmall raw st ctx hrep hwf hprot c hparse (Nat.lt_of_not_ge hgas) with
        hmatch | ⟨hout, hlogs⟩
      · exact Or.inl hmatch
      · exact Or.inr ⟨hout, nearRuntime_failure_rolledBack _ _ _ hout, hlogs⟩
  · intro hparse
    obtain ⟨failure, hout⟩ := hinvalid raw st ctx hrep hwf hprot hparse
    exact nearRuntime_failure_rolledBack _ _ _ hout

end Near.Boundary
