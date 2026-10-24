import NearRuntime.QueuedFunds

namespace Near
open Wasm Wasm.Near

def ChainState.receiptQueues (st : ChainState) : List (ReceiptId × Receipt) × List Receipt :=
  (st.postponed, st.delayed)

def Exec.receiptQueues (exec : Exec) := exec.state.receiptQueues

/-- An action operation cannot change the queues managed by receipt routing,
even when it fails after tentative account/storage changes. -/
def ExecM.PreservesReceiptQueues (operation : ExecM α) : Prop :=
  ∀ before, (operation.run.run before).2.receiptQueues = before.receiptQueues

theorem ExecM.PreservesReceiptQueues.bind {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.PreservesReceiptQueues) (hnext : ∀ value, (next value).PreservesReceiptQueues) :
    (operation >>= next).PreservesReceiptQueues := by
  intro before
  rw [execM_run_bind]
  have hp := hfirst before
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => exact hp
    | ok value => exact (hnext value middle).trans hp

theorem queues_pure (value : α) : (pure value : ExecM α).PreservesReceiptQueues := by intro before; rfl

theorem queues_throw (error : RuntimeError) : (throw error : ExecM α).PreservesReceiptQueues := by intro before; rfl

theorem queues_get : (get : ExecM Exec).PreservesReceiptQueues := by intro before; rfl

theorem queues_getState : getState.PreservesReceiptQueues := by intro before; rfl

theorem queues_getAccount (id : AccountId) : (getAccount id).PreservesReceiptQueues := by
  unfold getAccount
  apply ExecM.PreservesReceiptQueues.bind queues_getState
  intro st
  split
  · exact queues_pure _
  · exact queues_throw _

theorem commitFunctionCall_receiptQueues (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects) :
    (exec.commitFunctionCall outcome effects).receiptQueues = exec.receiptQueues := by
  have hf := congrArg ChainState.receiptQueues (commitFunctionCall_frame exec c account outcome isLast effects heffects)
  exact hf

theorem refundAllowance_receiptQueues (st : ChainState) (id : AccountId) (pk : PublicKey) (amount : Nat) :
    (st.refundAllowance id pk amount).receiptQueues = st.receiptQueues := by
  have hf := congrArg ChainState.receiptQueues (ChainState.refundAllowance_frame st id pk amount)
  exact hf

theorem transferCreditState_receiptQueues (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat) :
    (transferCreditState c st account amount).receiptQueues = st.receiptQueues := by
  unfold transferCreditState
  dsimp only
  split
  · exact refundAllowance_receiptQueues _ _ _ _
  · rfl

/-- Exact raw action unfoldings expose that only account/key/storage fields,
new receipt outputs and the id generator can change. -/
-- TODO(proof): adapt the cloned proof
theorem queues_applyAction (c : ReceiptCtx) (isLast : Bool) (action : Action) :
    (applyAction c isLast action).PreservesReceiptQueues := by
  sorry

theorem queues_burnGas (fee : Nat) : (burnGas fee).PreservesReceiptQueues := by intro before; rfl

theorem queues_fee (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).PreservesReceiptQueues := by
  exact queues_burnGas _

theorem queues_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).PreservesReceiptQueues := by
  unfold checkReceiptAction
  repeat (first
    | exact queues_pure _ | exact queues_throw _ | exact queues_get | exact queues_getState
    | (refine ExecM.PreservesReceiptQueues.bind ?_ (fun _ => ?_)) | split)

theorem queues_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).PreservesReceiptQueues := by
  unfold checkStorageStake
  repeat (first
    | exact queues_pure _ | exact queues_throw _ | exact queues_getState
    | (refine ExecM.PreservesReceiptQueues.bind ?_ (fun _ => ?_)) | split | (dsimp only; split))

theorem queues_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).PreservesReceiptQueues := by
  unfold runReceiptAction
  exact (queues_fee _ _).bind (fun _ => (queues_checkReceiptAction _ _ _).bind (fun _ => queues_applyAction _ _ _))

theorem queues_runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) (index : Nat) :
    (runReceiptActionAt c onlyAction isLast action index).PreservesReceiptQueues := by
  cases action <;> try exact queues_runReceiptAction _ _ _ _
  case functionCall method args gas deposit =>
    cases he : actionRandomSeed c index <;> simp only [runReceiptActionAt, he]
    · exact queues_throw _
    · exact queues_runReceiptAction _ _ _ _

theorem queues_failureIndex (index : Option Nat) :
    (modify fun e : Exec => { e with failureIndex := index } : ExecM Unit).PreservesReceiptQueues := by
  intro before; rfl

theorem queues_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) (index : Nat) :
    (runReceiptActionList c onlyAction actions index).PreservesReceiptQueues := by
  induction actions generalizing index with
  | nil => exact queues_pure _
  | cons action rest ih =>
    exact (queues_failureIndex _).bind (fun _ => (queues_runReceiptActionAt _ _ _ _ _).bind (fun _ => ih _))

theorem queues_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).PreservesReceiptQueues := by
  unfold receiptActionBody
  exact (queues_fee _ _).bind (fun _ => (queues_runReceiptActionList _ _ _ _).bind
    (fun _ => (queues_failureIndex _).bind (fun _ => queues_checkStorageStake _ _)))

theorem runReceiptActions_receiptQueues (c : ReceiptCtx) (st : ChainState) :
    (runReceiptActions c st).1.receiptQueues = st.receiptQueues := by
  have h := queues_receiptActionBody c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting }
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he, Exec.receiptQueues] using h

@[simp] theorem addBalanceRefund_receiptQueues (exec : Exec) (receiver : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).receiptQueues = exec.receiptQueues := rfl

@[simp] theorem addGasRefund_receiptQueues (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).receiptQueues = exec.receiptQueues := rfl

@[simp] theorem addFailureData_receiptQueues (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).receiptQueues = exec.receiptQueues := by
  unfold Exec.addFailureData
  dsimp only
  rw [failureDataFold_state]
  rfl

@[simp] theorem finishReceiptResult_receiptQueues (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) :
    (exec.finishReceiptResult c failed).receiptQueues = exec.receiptQueues := by
  unfold Exec.finishReceiptResult
  split <;> unfold Exec.deliverResult <;> dsimp only <;> split
  all_goals first
    | (simp only [Exec.addSuccessData, successDataFold_state]; rfl)
    | (simp only [addFailureData_receiptQueues] <;> rfl)
    | rfl

@[simp] theorem creditReceiptReward_receiptQueues (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).receiptQueues = exec.receiptQueues := by
  unfold Exec.creditReceiptReward
  split <;> rfl

@[simp] theorem setResult_receiptQueues (exec : Exec) (result : Option ExecutionStatus) :
    ({ exec with result } : Exec).receiptQueues = exec.receiptQueues := rfl

@[simp] theorem ite_receiptQueues (p : Prop) [Decidable p] (yes no : Exec) :
    (if p then yes else no).receiptQueues = if p then yes.receiptQueues else no.receiptQueues := by split <;> rfl

/-- Finalization preserves the routing-owned queues, including on rollback. -/
theorem finalizeReceipt_receiptQueues (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hraw : raw.receiptQueues = st.receiptQueues) :
    (finalizeReceipt c st raw failed).receiptQueues = st.receiptQueues := by
  unfold finalizeReceipt
  simp only [setResult_receiptQueues, finishReceiptResult_receiptQueues, creditReceiptReward_receiptQueues,
    ite_receiptQueues, addBalanceRefund_receiptQueues, addGasRefund_receiptQueues, ite_self]
  cases failed with
  | none => exact hraw
  | some error => rfl

theorem applyActionReceipt_receiptQueues (c : ReceiptCtx) (st : ChainState) :
    (applyActionReceipt c st).receiptQueues = st.receiptQueues :=
  finalizeReceipt_receiptQueues c st _ _ (runReceiptActions_receiptQueues c st)

theorem applyActionReceipt_queuedFunds (c : ReceiptCtx) (st : ChainState) :
    (applyActionReceipt c st).state.queuedFunds c.cfg = st.queuedFunds c.cfg := by
  have hf := congrArg (fun (queues : List (ReceiptId × Receipt) × List Receipt) =>
    Assoc.mass (Fees.receiptFunds c.cfg) queues.1 + receiptsFunds c.cfg queues.2)
    (applyActionReceipt_receiptQueues c st)
  exact hf

end Near
