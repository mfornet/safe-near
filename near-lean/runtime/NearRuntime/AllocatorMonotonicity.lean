import NearRuntime.ProcessorIdentifierBounds

namespace Near
open Wasm.Near

/-- Materialization reserves receipt and dependency ids without rewinding the
shared allocator. -/
theorem materializeFunctionCall_nextId_mono (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) : initial.nextId ≤ (materializeFunctionCallRaw c isLast outcome initial).state.nextId := by
  rw [materializeFunctionCallRaw_nextId]
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

-- TODO(proof): adapt the cloned proof
theorem commitFunctionCall_nextId_mono (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects) :
    exec.state.nextId ≤ (exec.commitFunctionCall outcome effects).state.nextId := by
  sorry

theorem refundAllowance_nextId (st : ChainState) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    (st.refundAllowance receiver pk amount).nextId = st.nextId := by
  have hf := congrArg ChainState.nextId (ChainState.refundAllowance_frame st receiver pk amount)
  exact hf

theorem transferCreditState_nextId (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat) :
    (transferCreditState c st account amount).nextId = st.nextId := by
  unfold transferCreditState
  split
  · exact refundAllowance_nextId _ _ _ _
  · rfl

/-- Even failed raw action attempts never rewind the allocator. Receipt rollback
is handled separately relative to the receipt's initial state. -/
-- TODO(proof): adapt the cloned proof
theorem applyAction_nextId_mono (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec) :
    before.state.nextId ≤ ((applyAction c isLast action).run.run before).2.state.nextId := by
  sorry

/-- Counter progress composes through the same action monad on all outcomes. -/
def ExecM.NextIdMonotone (operation : ExecM α) : Prop :=
  ∀ before, before.state.nextId ≤ (operation.run.run before).2.state.nextId

theorem ExecM.NextIdMonotone.bind {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.NextIdMonotone) (hnext : ∀ value, (next value).NextIdMonotone) :
    (operation >>= next).NextIdMonotone := by
  intro before
  rw [execM_run_bind]
  have hp := hfirst before
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => exact hp
    | ok value => exact hp.trans (hnext value middle)

theorem nextId_pure (value : α) : (pure value : ExecM α).NextIdMonotone := by intro before; exact Nat.le_refl _
theorem nextId_throw (error : RuntimeError) : (throw error : ExecM α).NextIdMonotone := by intro before; exact Nat.le_refl _
theorem nextId_get : (get : ExecM Exec).NextIdMonotone := by intro before; exact Nat.le_refl _
theorem nextId_getState : getState.NextIdMonotone := by intro before; exact Nat.le_refl _

theorem nextId_fee (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).NextIdMonotone := by
  intro before
  unfold chargeReceiptFee burnGas
  exact Nat.le_refl _

theorem nextId_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).NextIdMonotone := by
  unfold checkReceiptAction
  refine ExecM.NextIdMonotone.bind nextId_getState (fun st => ?_)
  split
  · exact nextId_throw _
  · refine ExecM.NextIdMonotone.bind nextId_get (fun before => ?_)
    split
    · exact nextId_throw _
    · exact nextId_pure _

theorem nextId_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).NextIdMonotone := by
  unfold checkStorageStake
  refine ExecM.NextIdMonotone.bind nextId_getState (fun st => ?_)
  split
  · dsimp only
    split
    · exact nextId_throw _
    · exact nextId_pure _
  · exact nextId_pure _

theorem nextId_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).NextIdMonotone := by
  unfold runReceiptAction
  exact (nextId_fee _ _).bind (fun _ => (nextId_checkReceiptAction _ _ _).bind
    (fun _ => applyAction_nextId_mono _ _ _))

-- TODO(proof): adapt the cloned proof
theorem nextId_runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool)
    (action : Action) (index : Nat) : (runReceiptActionAt c onlyAction isLast action index).NextIdMonotone := by
  sorry

theorem nextId_failureIndex (index : Option Nat) :
    (modify fun e => { e with failureIndex := index } : ExecM Unit).NextIdMonotone := by
  intro before
  exact Nat.le_refl _

theorem nextId_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action)
    (index : Nat) : (runReceiptActionList c onlyAction actions index).NextIdMonotone := by
  induction actions generalizing index with
  | nil => exact nextId_pure _
  | cons action rest ih =>
    exact (nextId_failureIndex (some index)).bind (fun _ =>
      (nextId_runReceiptActionAt c onlyAction rest.isEmpty action index).bind (fun _ => ih (index + 1)))

theorem nextId_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).NextIdMonotone := by
  unfold receiptActionBody
  exact (nextId_fee _ _).bind (fun _ => (nextId_runReceiptActionList _ _ _ _).bind
    (fun _ => (nextId_failureIndex none).bind (fun _ => nextId_checkStorageStake _ _)))

theorem runReceiptActions_nextId_mono (c : ReceiptCtx) (st : ChainState) :
    st.nextId ≤ (runReceiptActions c st).1.state.nextId := by
  have hp := nextId_receiptActionBody c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting }
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he] using hp

theorem Exec.addBalanceRefund_nextId_mono (exec : Exec) (receiver : AccountId) (amount : Nat) :
    exec.state.nextId ≤ (exec.addBalanceRefund receiver amount).state.nextId := Nat.le_succ _

theorem Exec.addGasRefund_nextId_mono (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    exec.state.nextId ≤ (exec.addGasRefund receiver pk amount).state.nextId := Nat.le_succ _

theorem Exec.addFailureData_nextId_mono (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    exec.state.nextId ≤ (exec.addFailureData receiver outputs).state.nextId := by
  unfold Exec.addFailureData
  dsimp only
  rw [failureDataFold_state]
  exact Nat.le_add_right _ _

theorem Exec.finishReceiptResult_nextId_mono (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) :
    exec.state.nextId ≤ (exec.finishReceiptResult c failed).state.nextId := by
  unfold Exec.finishReceiptResult
  split <;> unfold Exec.deliverResult <;> dsimp only <;> split
  all_goals first
    | (simp only [Exec.addSuccessData, successDataFold_state]; exact Nat.le_add_right _ _)
    | exact Exec.addFailureData_nextId_mono _ _ _
    | exact Nat.le_refl _

theorem Exec.creditReceiptReward_nextId (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.nextId = exec.state.nextId := by
  unfold Exec.creditReceiptReward
  split <;> rfl

/-- Rollback may discard speculative allocations, but finalization never rewinds
past the receipt's initial counter. -/
-- TODO(proof): adapt the cloned proof
theorem finalizeReceipt_nextId_mono (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hraw : st.nextId ≤ raw.state.nextId) :
    st.nextId ≤ (finalizeReceipt c st raw failed).state.nextId := by
  sorry

theorem applyActionReceipt_nextId_mono (c : ReceiptCtx) (st : ChainState) :
    st.nextId ≤ (applyActionReceipt c st).state.nextId :=
  finalizeReceipt_nextId_mono c st _ _ (runReceiptActions_nextId_mono c st)

/-- Every processor path advances or retains the allocator, including recursive
release and unsupported/incomplete fallback. No well-formedness premise is used. -/
-- TODO(proof): adapt the cloned proof
theorem processReceipt_nextId_mono (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) : st.nextId ≤ (processReceipt cfg ap decoder st receipt).state.nextId := by
  sorry

end Near
