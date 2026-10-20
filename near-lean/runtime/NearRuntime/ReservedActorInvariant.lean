import NearRuntime.ActionAccountFrame
import NearRuntime.TransactionInvariants

namespace Near
open Wasm.Near

/-- The protocol's synthetic sender is not an ordinary stored account. -/
def ChainState.SystemAccountAbsent (st : ChainState) : Prop := st.account? systemAccount = none

@[simp] theorem implicitPublicKey_system : implicitPublicKey? systemAccount = none := by decide

/-- No raw action creates the reserved actor. The direct-target case uses real
creation rejection and the fact that the name is not an implicit public key. -/
theorem applyAction_systemAbsent (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (hmissing : before.state.SystemAccountAbsent) :
    ((applyAction c isLast action).run.run before).2.state.SystemAccountAbsent := by
  change before.state.account? systemAccount = none at hmissing
  change ((applyAction c isLast action).run.run before).2.state.account? systemAccount = none
  by_cases hreceiver : c.receipt.receiverId = systemAccount
  · cases action with
    | createAccount => rw [applyCreateAccount_run]; simp [hreceiver, hmissing]
    | deployContract code => rw [applyDeployContract_run]; simp [hreceiver, hmissing]
    | functionCall method args gas deposit =>
      change ((applyFunctionCall c method args gas deposit isLast).run.run before).2.state.account? systemAccount = none
      rw [applyFunctionCall_run]
      simp [hreceiver, hmissing]
    | transfer amount =>
      rw [applyTransfer_run]
      simp only [hreceiver, hmissing, implicitPublicKey_system]
      split <;> exact hmissing
    | stake amount pk =>
      simp [-ExceptT.run_bind, -StateT.run_bind, applyAction, getAccount, getState, hreceiver, hmissing]
    | addKey pk key =>
      rw [applyAddKey_run]
      simp only [hreceiver, hmissing]
      split <;> exact hmissing
    | deleteKey pk =>
      rw [applyDeleteKey_run]
      simp only [hreceiver, hmissing]
      split <;> exact hmissing
    | deleteAccount beneficiary =>
      rw [applyDeleteAccount_run]
      simp only [hreceiver, hmissing]
      split <;> exact hmissing
  · exact (applyAction_account_ne c isLast action before systemAccount hreceiver).trans hmissing

/-- The invariant is required after failures as well as successes, so it can
compose through arbitrary action sequences before receipt rollback. -/
def ExecM.PreservesSystemAbsence (operation : ExecM α) : Prop :=
  ∀ before, before.state.SystemAccountAbsent → (operation.run.run before).2.state.SystemAccountAbsent

theorem ExecM.PreservesSystemAbsence.bind {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.PreservesSystemAbsence) (hnext : ∀ value, (next value).PreservesSystemAbsence) :
    (operation >>= next).PreservesSystemAbsence := by
  intro before hmissing
  rw [execM_run_bind]
  have hp := hfirst before hmissing
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => exact hp
    | ok value => exact hnext value middle hp

theorem systemAbsence_pure (value : α) : (pure value : ExecM α).PreservesSystemAbsence := by intro before h; exact h

theorem systemAbsence_throw (error : RuntimeError) : (throw error : ExecM α).PreservesSystemAbsence := by intro before h; exact h

theorem systemAbsence_get : (get : ExecM Exec).PreservesSystemAbsence := by intro before h; exact h

theorem systemAbsence_getState : getState.PreservesSystemAbsence := by intro before h; exact h

theorem systemAbsence_fee (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).PreservesSystemAbsence := by
  intro before h
  unfold chargeReceiptFee
  split <;> exact h

theorem systemAbsence_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).PreservesSystemAbsence := by
  unfold checkReceiptAction
  repeat (first
    | exact systemAbsence_pure _ | exact systemAbsence_throw _ | exact systemAbsence_get | exact systemAbsence_getState
    | (refine ExecM.PreservesSystemAbsence.bind ?_ (fun _ => ?_)) | split)

theorem systemAbsence_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).PreservesSystemAbsence := by
  unfold checkStorageStake
  repeat (first
    | exact systemAbsence_pure _ | exact systemAbsence_throw _ | exact systemAbsence_getState
    | (refine ExecM.PreservesSystemAbsence.bind ?_ (fun _ => ?_)) | split | (dsimp only; split))

theorem systemAbsence_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).PreservesSystemAbsence := by
  unfold runReceiptAction
  exact (systemAbsence_fee _ _).bind (fun _ => (systemAbsence_checkReceiptAction _ _ _).bind
    (fun _ => applyAction_systemAbsent _ _ _))

theorem systemAbsence_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) :
    (runReceiptActionList c onlyAction actions).PreservesSystemAbsence := by
  induction actions with
  | nil => exact systemAbsence_pure _
  | cons action rest ih => exact (systemAbsence_runReceiptAction _ _ _ _).bind (fun _ => ih)

theorem systemAbsence_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).PreservesSystemAbsence := by
  unfold receiptActionBody
  exact (systemAbsence_fee _ _).bind (fun _ => (systemAbsence_runReceiptActionList _ _ _).bind
    (fun _ => systemAbsence_checkStorageStake _ _))

theorem runReceiptActions_systemAbsent (c : ReceiptCtx) (st : ChainState) (h : st.SystemAccountAbsent) :
    (runReceiptActions c st).1.state.SystemAccountAbsent := by
  have hp := systemAbsence_receiptActionBody c { state := st, actorId := c.receipt.predecessorId } h
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he] using hp

theorem Exec.creditReceiptReward_systemAbsent (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (h : exec.state.SystemAccountAbsent) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.SystemAccountAbsent := by
  change exec.state.account? systemAccount = none at h
  change (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.account? systemAccount = none
  unfold Exec.creditReceiptReward
  split
  · rename_i account haccount
    by_cases hr : receiver = systemAccount
    · rw [hr, h] at haccount
      contradiction
    · exact (ChainState.account?_setAccount_ne _ _ _ _ hr).trans h
  · exact h

/-- Rewards and refunds cannot install an absent system account. Even a reward
targeting the name is skipped because no such receiver account exists. -/
theorem finalizeReceipt_systemAbsent (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hinitial : st.SystemAccountAbsent) (hraw : raw.state.SystemAccountAbsent) :
    (finalizeReceipt c st raw failed).state.SystemAccountAbsent := by
  cases failed <;> unfold finalizeReceipt rollbackReceipt ChainState.SystemAccountAbsent <;> dsimp only
  all_goals repeat' (first
    | exact hinitial | exact hraw
    | apply Exec.creditReceiptReward_systemAbsent
    | rw [finishReceiptResult_account]
    | rw [addFailureData_account]
    | rw [addGasRefund_account]
    | rw [addBalanceRefund_account]
    | split)

theorem applyActionReceipt_systemAbsent (c : ReceiptCtx) (st : ChainState) (h : st.SystemAccountAbsent) :
    (applyActionReceipt c st).state.SystemAccountAbsent :=
  finalizeReceipt_systemAbsent c st _ _ h (runReceiptActions_systemAbsent c st h)

/-- Processing any receipt preserves absence of the synthetic actor, even when
malformed stored data receipts recursively release further postponed work. -/
theorem processReceipt_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (h : st.SystemAccountAbsent) :
    (processReceipt cfg ap decoder st receipt).state.SystemAccountAbsent := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action hr he]
      exact h
    | true =>
      rw [processReceipt_ready cfg ap decoder st receipt action hr he]
      unfold processedOfExec
      split
      · exact h
      · exact applyActionReceipt_systemAbsent _ _ h
  | data data =>
    rw [processReceipt_data cfg ap decoder st receipt data hr]
    cases hroute : Assoc.lookup st.postponedByData data.dataId with
    | none => exact h
    | some id =>
      simp only
      cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
      | false => simp only [Bool.false_eq_true, ite_false]; exact h
      | true =>
        simp only [ite_true]
        cases hwaiting : Assoc.lookup st.postponed id with
        | none => exact h
        | some waiting =>
          exact processReceipt_systemAbsent cfg ap decoder
            (releasePostponedState (receivePostponedDataState st data) id) waiting h
termination_by st.postponed.length
decreasing_by
  exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

/-- An absent synthetic actor cannot authenticate a transaction; successful
conversion can therefore update only an ordinary signer account. -/
theorem convertTransaction_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : st.SystemAccountAbsent)
    (hconvert : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    st'.SystemAccountAbsent := by
  obtain ⟨signer, _, hsigner, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost hconvert
  have hne : tx.signerId ≠ systemAccount := by
    intro he
    rw [he, h] at hsigner
    contradiction
  exact (convertTransaction_account_frame cfg ap st st' tx receipt cost systemAccount hne hconvert).trans h

/-- The local financial state invariant also excludes a stored synthetic actor.
Input scope and successful support remain explicit accounting premises. -/
def ChainState.RuntimeFundingInvariant (st : ChainState) : Prop :=
  st.ReceiptFundingInvariant ∧ st.SystemAccountAbsent

theorem processReceipt_runtimeFundingInvariant (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt)
    (h : st.RuntimeFundingInvariant) (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.RuntimeFundingInvariant :=
  ⟨processReceipt_fundingInvariant cfg ap decoder st receipt h.1 hshape hsupported,
    processReceipt_systemAbsent cfg ap decoder st receipt h.2⟩

end Near
