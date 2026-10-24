import NearRuntime.RoutingIdentifierBounds
import NearRuntime.FinalizeStages

namespace Near
open Wasm.Near


theorem commitFunctionCall_idsBelowNext (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects)
    (h : exec.state.IdsBelowNext) :
    (exec.commitFunctionCall outcome effects).state.IdsBelowNext := by
  change effects.state.IdsBelowNext
  rw [functionCallEffects_success c account outcome isLast exec.state effects heffects]
  exact materializeFunctionCall_idsBelowNext c isLast outcome _ h

theorem refundAllowance_idsBelowNext (st : ChainState) (receiver : AccountId) (pk : PublicKey) (amount : Nat)
    (h : st.IdsBelowNext) : (st.refundAllowance receiver pk amount).IdsBelowNext := by
  unfold ChainState.refundAllowance
  split
  · exact h
  · split <;> exact h

theorem transferCreditState_idsBelowNext (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat)
    (h : st.IdsBelowNext) : (transferCreditState c st account amount).IdsBelowNext := by
  unfold transferCreditState
  split
  · exact refundAllowance_idsBelowNext _ _ _ _ h
  · exact h

/-- Every raw action preserves the allocator bound, on failures as well as
successes. Account changes do not alter routing references. -/
theorem applyAction_idsBelowNext (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (h : before.state.IdsBelowNext) : ((applyAction c isLast action).run.run before).2.state.IdsBelowNext := by
  cases action with
  | createAccount => rw [applyCreateAccount_run]; repeat' (first | exact h | split)
  | deployContract code => rw [applyDeployContract_run]; repeat' (first | exact h | split)
  | functionCall method args gas deposit =>
    rw [show applyAction c isLast (.functionCall method args gas deposit) =
      applyFunctionCall c method args gas deposit isLast from rfl, applyFunctionCall_run]
    cases ha : before.state.account? c.receipt.receiverId with
    | none => exact h
    | some account =>
      dsimp only
      cases hc : account.code with
      | none => exact h
      | some code =>
        dsimp only
        cases hi : code.decodeIssue with
        | some issue => exact h
        | none =>
          dsimp only
          generalize ho : run c.cfg code.module code.size method
            (functionCallContext c account args gas deposit isLast before.storageAccounting)
            (before.state.contractStorage c.receipt.receiverId) = outcome
          cases he : outcome.aborted with
          | some error => exact h
          | none =>
            dsimp only
            cases hf : functionCallEffects c account outcome isLast before.state with
            | error error => exact h
            | ok effects =>
              exact commitFunctionCall_idsBelowNext (before.recordVMOutcome outcome) c account outcome isLast effects hf h
  | transfer amount =>
    rw [applyTransfer_run]
    split
    · exact transferCreditState_idsBelowNext _ _ _ _ h
    · split
      · exact h
      · split <;> exact h
  | stake amount pk =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-StateT.run_bind, applyAction, getAccount, getState, ha]
    repeat' (first | exact h | split)
  | addKey pk key => rw [applyAddKey_run]; repeat' (first | exact h | split)
  | deleteKey pk => rw [applyDeleteKey_run]; repeat' (first | exact h | split)
  | useGlobalContract _ => exact h
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    repeat' (first | exact h | exact h.freshId | split)

/-- The invariant is required after failures as well as successes, so it can
compose through arbitrary action sequences before receipt rollback. -/
def ExecM.PreservesIdBounds (operation : ExecM α) : Prop :=
  ∀ before, before.state.IdsBelowNext → (operation.run.run before).2.state.IdsBelowNext

theorem ExecM.PreservesIdBounds.bind {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.PreservesIdBounds) (hnext : ∀ value, (next value).PreservesIdBounds) :
    (operation >>= next).PreservesIdBounds := by
  intro before hmissing
  rw [execM_run_bind]
  have hp := hfirst before hmissing
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => exact hp
    | ok value => exact hnext value middle hp

theorem idBounds_pure (value : α) : (pure value : ExecM α).PreservesIdBounds := by intro before h; exact h

theorem idBounds_throw (error : RuntimeError) : (throw error : ExecM α).PreservesIdBounds := by intro before h; exact h

theorem idBounds_get : (get : ExecM Exec).PreservesIdBounds := by intro before h; exact h

theorem idBounds_getState : getState.PreservesIdBounds := by intro before h; exact h

theorem idBounds_fee (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).PreservesIdBounds := by
  intro before h
  unfold chargeReceiptFee burnGas
  exact h

theorem idBounds_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).PreservesIdBounds := by
  unfold checkReceiptAction
  refine ExecM.PreservesIdBounds.bind idBounds_getState (fun st => ?_)
  split
  · exact idBounds_throw _
  · refine ExecM.PreservesIdBounds.bind idBounds_get (fun before => ?_)
    split
    · exact idBounds_throw _
    · exact idBounds_pure _

theorem idBounds_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).PreservesIdBounds := by
  unfold checkStorageStake
  refine ExecM.PreservesIdBounds.bind idBounds_getState (fun st => ?_)
  split
  · dsimp only
    split
    · exact idBounds_throw _
    · exact idBounds_pure _
  · exact idBounds_pure _

theorem idBounds_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).PreservesIdBounds := by
  unfold runReceiptAction
  exact (idBounds_fee _ _).bind (fun _ => (idBounds_checkReceiptAction _ _ _).bind
    (fun _ => applyAction_idsBelowNext _ _ _))

theorem idBounds_runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool)
    (action : Action) (index : Nat) : (runReceiptActionAt c onlyAction isLast action index).PreservesIdBounds := by
  cases action with
  | createAccount  => exact idBounds_runReceiptAction c onlyAction isLast (.createAccount)
  | deployContract code => exact idBounds_runReceiptAction c onlyAction isLast (.deployContract code)
  | transfer amount => exact idBounds_runReceiptAction c onlyAction isLast (.transfer amount)
  | stake amount pk => exact idBounds_runReceiptAction c onlyAction isLast (.stake amount pk)
  | addKey pk key => exact idBounds_runReceiptAction c onlyAction isLast (.addKey pk key)
  | deleteKey pk => exact idBounds_runReceiptAction c onlyAction isLast (.deleteKey pk)
  | useGlobalContract contract => exact idBounds_runReceiptAction c onlyAction isLast (.useGlobalContract contract)
  | deleteAccount beneficiary => exact idBounds_runReceiptAction c onlyAction isLast (.deleteAccount beneficiary)
  | functionCall method args gas deposit =>
    cases hs : actionRandomSeed c index with
    | error error =>
      simp only [runReceiptActionAt, hs]
      exact idBounds_throw _
    | ok seed =>
      simp only [runReceiptActionAt, hs]
      exact idBounds_runReceiptAction _ _ _ _

theorem idBounds_failureIndex (index : Option Nat) :
    (modify fun e => { e with failureIndex := index } : ExecM Unit).PreservesIdBounds := by
  intro before h
  exact h

theorem idBounds_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action)
    (index : Nat) : (runReceiptActionList c onlyAction actions index).PreservesIdBounds := by
  induction actions generalizing index with
  | nil => exact idBounds_pure _
  | cons action rest ih =>
    exact (idBounds_failureIndex (some index)).bind (fun _ =>
      (idBounds_runReceiptActionAt c onlyAction rest.isEmpty action index).bind (fun _ => ih (index + 1)))

theorem idBounds_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).PreservesIdBounds := by
  unfold receiptActionBody
  exact (idBounds_fee _ _).bind (fun _ => (idBounds_runReceiptActionList _ _ _ _).bind
    (fun _ => (idBounds_failureIndex none).bind (fun _ => idBounds_checkStorageStake _ _)))

theorem runReceiptActions_idsBelowNext (c : ReceiptCtx) (st : ChainState) (h : st.IdsBelowNext) :
    (runReceiptActions c st).1.state.IdsBelowNext := by
  have hp := idBounds_receiptActionBody c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } h
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he] using hp


theorem Exec.addBalanceRefund_idsBelowNext (exec : Exec) (receiver : AccountId) (amount : Nat)
    (h : exec.state.IdsBelowNext) : (exec.addBalanceRefund receiver amount).state.IdsBelowNext := h.freshId

theorem Exec.addGasRefund_idsBelowNext (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat)
    (h : exec.state.IdsBelowNext) : (exec.addGasRefund receiver pk amount).state.IdsBelowNext := h.freshId

theorem Exec.addFailureData_idsBelowNext (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (h : exec.state.IdsBelowNext) : (exec.addFailureData receiver outputs).state.IdsBelowNext := by
  unfold Exec.addFailureData
  dsimp only
  apply foldl_preserves (fun pair : ChainState × List Receipt => pair.1.IdsBelowNext)
  · intro pair item hp
    exact hp.freshId
  · exact h

theorem Exec.addSuccessData_idsBelowNext (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) (bytes : Bytes)
    (h : exec.state.IdsBelowNext) : (exec.addSuccessData receiver outputs bytes).state.IdsBelowNext := by
  unfold Exec.addSuccessData
  dsimp only
  apply foldl_preserves (fun pair : ChainState × List Receipt => pair.1.IdsBelowNext)
  · intro pair item hp
    exact hp.freshId
  · exact h

theorem Exec.deliverResult_idsBelowNext (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (h : exec.state.IdsBelowNext) : (exec.deliverResult receiver outputs).state.IdsBelowNext := by
  unfold Exec.deliverResult
  split
  · exact Exec.addSuccessData_idsBelowNext _ _ _ _ h
  · exact Exec.addFailureData_idsBelowNext _ _ _ h
  · exact h

theorem Exec.finishReceiptResult_idsBelowNext (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError)
    (h : exec.state.IdsBelowNext) : (exec.finishReceiptResult c failed).state.IdsBelowNext := by
  unfold Exec.finishReceiptResult
  apply Exec.deliverResult_idsBelowNext
  split <;> exact h

theorem Exec.creditReceiptReward_idsBelowNext (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (h : exec.state.IdsBelowNext) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.IdsBelowNext := by
  unfold Exec.creditReceiptReward
  split <;> exact h

/-- Finalization may allocate refunds and failure envelopes; none of these
operations changes old routing references or moves the counter backwards. -/
theorem finalizeReceipt_idsBelowNext (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hinitial : st.IdsBelowNext) (hraw : raw.state.IdsBelowNext) :
    (finalizeReceipt c st raw failed).state.IdsBelowNext := by
  refine finalizeReceipt_stages (fun e => e.state.IdsBelowNext) c st raw failed ?_
    (fun _ _ _ h => h)
    (fun e _ _ h => Exec.addBalanceRefund_idsBelowNext e _ _ h)
    (fun e _ _ _ h => Exec.addGasRefund_idsBelowNext e _ _ _ h)
    (fun e _ _ h => Exec.creditReceiptReward_idsBelowNext e _ _ _ _ h)
    (fun e h => Exec.finishReceiptResult_idsBelowNext e c failed h)
    (fun _ _ h => h)
  cases failed <;> first | exact hraw | exact hinitial

theorem applyActionReceipt_idsBelowNext (c : ReceiptCtx) (st : ChainState) (h : st.IdsBelowNext) :
    (applyActionReceipt c st).state.IdsBelowNext :=
  finalizeReceipt_idsBelowNext c st _ _ h (runReceiptActions_idsBelowNext c st h)

end Near
