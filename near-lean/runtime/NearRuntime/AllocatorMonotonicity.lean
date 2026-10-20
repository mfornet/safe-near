import NearRuntime.ProcessorIdentifierBounds

namespace Near
open Wasm.Near

/-- Materialization reserves receipt and dependency ids without rewinding the
shared allocator. -/
theorem materializeFunctionCall_nextId_mono (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) : initial.nextId ≤ (materializeFunctionCall c isLast outcome initial).state.nextId := by
  rw [materializeFunctionCall_nextId]
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem commitFunctionCall_nextId_mono (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) :
    exec.state.nextId ≤ (exec.commitFunctionCall c account outcome isLast).state.nextId :=
  materializeFunctionCall_nextId_mono c isLast outcome
    ((exec.state.setAccount c.receipt.receiverId
      { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
        c.receipt.receiverId outcome.storage)

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
theorem applyAction_nextId_mono (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec) :
    before.state.nextId ≤ ((applyAction c isLast action).run.run before).2.state.nextId := by
  cases action with
  | createAccount => rw [applyCreateAccount_run]; repeat' (first | exact Nat.le_refl _ | split)
  | deployContract code => rw [applyDeployContract_run]; repeat' (first | exact Nat.le_refl _ | split)
  | functionCall method args gas deposit =>
    rw [show applyAction c isLast (.functionCall method args gas deposit) =
      applyFunctionCall c method args gas deposit isLast from rfl, applyFunctionCall_run]
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · dsimp only
        split
        · exact Nat.le_refl _
        · exact commitFunctionCall_nextId_mono _ _ _ _ _
  | transfer amount =>
    rw [applyTransfer_run]
    split
    · exact Nat.le_of_eq (transferCreditState_nextId _ _ _ _).symm
    · split
      · exact Nat.le_refl _
      · split <;> exact Nat.le_refl _
  | stake amount pk =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-ExceptT.run_bind, -StateT.run_bind, applyAction, getAccount, getState, ha]
    repeat' (first | exact Nat.le_refl _ | split)
  | addKey pk key => rw [applyAddKey_run]; repeat' (first | exact Nat.le_refl _ | split)
  | deleteKey pk => rw [applyDeleteKey_run]; repeat' (first | exact Nat.le_refl _ | split)
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    repeat' (first | exact Nat.le_refl _ | exact Nat.le_succ _ | split)

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
  unfold chargeReceiptFee
  split <;> exact Nat.le_refl _

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

theorem nextId_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) :
    (runReceiptActionList c onlyAction actions).NextIdMonotone := by
  induction actions with
  | nil => exact nextId_pure _
  | cons action rest ih => exact (nextId_runReceiptAction _ _ _ _).bind (fun _ => ih)

theorem nextId_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).NextIdMonotone := by
  unfold receiptActionBody
  exact (nextId_fee _ _).bind (fun _ => (nextId_runReceiptActionList _ _ _).bind
    (fun _ => nextId_checkStorageStake _ _))

theorem runReceiptActions_nextId_mono (c : ReceiptCtx) (st : ChainState) :
    st.nextId ≤ (runReceiptActions c st).1.state.nextId := by
  have hp := nextId_receiptActionBody c { state := st, actorId := c.receipt.predecessorId }
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId } with
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
theorem finalizeReceipt_nextId_mono (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hraw : st.nextId ≤ raw.state.nextId) :
    st.nextId ≤ (finalizeReceipt c st raw failed).state.nextId := by
  let base := rollbackReceipt st raw failed
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) base.gasUsed base.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (base.state.account? c.receipt.receiverId).isSome && failed.isNone)
  let charged := { base with
    tokensBurnt := if c.receipt.isRefund then 0 else settlement.tokensBurnt
    otherTokensBurnt := if c.receipt.isRefund && failed.isSome then Fees.totalDeposit c.action.actions else 0 }
  let depositRefund := if failed.isSome then Fees.totalDeposit c.action.actions else 0
  let gasRefund := if c.receipt.isRefund then 0 else settlement.refund
  let balance := if depositRefund > 0 && c.receipt.predecessorId != systemAccount then
    charged.addBalanceRefund c.receipt.predecessorId depositRefund else charged
  let gas := if gasRefund > 0 && c.action.signerId != systemAccount then
    balance.addGasRefund c.action.signerId c.action.signerPublicKey gasRefund else balance
  let rewarded := gas.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let finished := rewarded.finishReceiptResult c failed
  have hbase : st.nextId ≤ base.state.nextId := by
    cases failed <;> first | exact hraw | exact Nat.le_refl _
  have hcharged : st.nextId ≤ charged.state.nextId := hbase
  have hbalance : st.nextId ≤ balance.state.nextId := by
    dsimp only [balance]
    split
    · exact hcharged.trans (Exec.addBalanceRefund_nextId_mono charged _ _)
    · exact hcharged
  have hgas : st.nextId ≤ gas.state.nextId := by
    dsimp only [gas]
    split
    · exact hbalance.trans (Exec.addGasRefund_nextId_mono balance _ _ _)
    · exact hbalance
  have hrewarded : st.nextId ≤ rewarded.state.nextId := by
    rw [Exec.creditReceiptReward_nextId]
    exact hgas
  have hfinished : st.nextId ≤ finished.state.nextId := by
    exact hrewarded.trans (Exec.finishReceiptResult_nextId_mono rewarded c failed)
  exact hfinished

theorem applyActionReceipt_nextId_mono (c : ReceiptCtx) (st : ChainState) :
    st.nextId ≤ (applyActionReceipt c st).state.nextId :=
  finalizeReceipt_nextId_mono c st _ _ (runReceiptActions_nextId_mono c st)

/-- Every processor path advances or retains the allocator, including recursive
release and unsupported/incomplete fallback. No well-formedness premise is used. -/
theorem processReceipt_nextId_mono (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) : st.nextId ≤ (processReceipt cfg ap decoder st receipt).state.nextId := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action hr he]
      exact Nat.le_refl _
    | true =>
      rw [processReceipt_ready cfg ap decoder st receipt action hr he]
      unfold processedOfExec
      split
      · exact Nat.le_refl _
      · exact applyActionReceipt_nextId_mono (readyActionContext cfg ap decoder st receipt action)
          (consumeReceiptDataState st action)
  | data data =>
    rw [processReceipt_data cfg ap decoder st receipt data hr]
    cases hroute : Assoc.lookup st.postponedByData data.dataId with
    | none => exact Nat.le_refl _
    | some id =>
      simp only
      cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
      | false => simp only [Bool.false_eq_true, ite_false]; exact Nat.le_refl _
      | true =>
        simp only [ite_true]
        cases hwaiting : Assoc.lookup st.postponed id with
        | none => exact Nat.le_refl _
        | some waiting =>
          exact processReceipt_nextId_mono cfg ap decoder
            (releasePostponedState (receivePostponedDataState st data) id) waiting
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

end Near
