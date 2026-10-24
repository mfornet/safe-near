import NearRuntime.ActionAccountFrame
import NearRuntime.TransactionInvariants

namespace Near
open Wasm.Near

/-- The protocol's synthetic sender is not an ordinary stored account. -/
def ChainState.SystemAccountAbsent (st : ChainState) : Prop := st.account? systemAccount = none

@[simp] theorem implicitPublicKey_system : implicitPublicKey? systemAccount = none := by decide

theorem specialImplicitAccount_system (c : ReceiptCtx) (deposit : Nat) :
    specialImplicitAccount c systemAccount deposit = .ok none := by
  unfold specialImplicitAccount
  split
  · rfl
  · have hk : accountKind (bytesOfString systemAccount) = .named := by
      unfold systemAccount bytesOfString
      decide +kernel
    rw [hk]

theorem gasKeyWithdrawal_systemAbsent {st moved : ChainState} {id : AccountId} {pk : PublicKey} {amount : Nat}
    (h : gasKeyWithdrawal st id pk amount = .ok moved) (hmissing : st.account? systemAccount = none) :
    moved.account? systemAccount = none := by
  by_cases hid : id = systemAccount
  · have := (gasKeyWithdrawal_account h).1
    rw [hid, hmissing] at this
    cases this
  · exact ((gasKeyWithdrawal_account h).2 systemAccount hid).trans hmissing

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
    | deployContract code =>
      rw [applyDeployContract_run]
      simp [hreceiver, hmissing]
      split <;> exact hmissing
    | functionCall method args gas deposit =>
      change ((applyFunctionCall c method args gas deposit isLast).run.run before).2.state.account? systemAccount = none
      rw [applyFunctionCall_run]
      simp [hreceiver, hmissing]
    | transfer amount =>
      rw [applyTransfer_run]
      simp only [hreceiver, hmissing, specialImplicitAccount_system, implicitPublicKey_system]
    | stake amount pk =>
      simp [-StateT.run_bind, applyAction, getAccount, getState, hreceiver, hmissing]
    | addKey pk key =>
      rw [applyAddKey_run]
      simp only [hreceiver, hmissing]
      split <;> exact hmissing
    | deleteKey pk =>
      rw [applyDeleteKey_run]
      simp only [hreceiver, hmissing]
      split <;> exact hmissing
    | useGlobalContract contract =>
      rw [applyUseGlobalContract_run]
      simp only [hreceiver, hmissing]
      repeat' (first | exact hmissing | split)
    | deployGlobalContract code mode =>
      rw [applyDeployGlobalContract_run]
      simp only [hreceiver, hmissing]
    | transferToGasKey pk deposit =>
      rw [applyTransferToGasKey_run]
      repeat' (first | exact hmissing | exact (gasKeyDeposit_account (by assumption) _).trans hmissing | split)
    | withdrawFromGasKey pk amount =>
      rw [applyWithdrawFromGasKey_run]
      repeat' (first | exact hmissing | exact gasKeyWithdrawal_systemAbsent (by assumption) hmissing | split)
    | deleteAccount beneficiary =>
      rw [applyDeleteAccount_run]
      simp only [hreceiver, hmissing]
      split <;> exact hmissing
    | delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2 =>
      change ((applyDelegateAction c _).run.run before).2.state.account? systemAccount = none
      rw [applyDelegateAction_run]
      repeat' (first | exact hmissing | split)
      all_goals
        dsimp only
        rw [delegateResult_account]
        have h := delegateState_account (by assumption) systemAccount
        exact h.trans hmissing
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
  unfold chargeReceiptFee burnGas
  exact h

theorem systemAbsence_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).PreservesSystemAbsence := by
  unfold checkReceiptAction
  repeat (first
    | exact systemAbsence_pure _ | exact systemAbsence_throw _ | exact systemAbsence_get | exact systemAbsence_getState
    | (refine ExecM.PreservesSystemAbsence.bind ?_ (fun _ => ?_)) | split)

theorem systemAbsence_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).PreservesSystemAbsence := by
  unfold checkStorageStake
  refine ExecM.PreservesSystemAbsence.bind systemAbsence_getState (fun st => ?_)
  cases st.account? id with
  | none => exact systemAbsence_pure _
  | some a =>
    dsimp only
    by_cases hd : storageStakeDeficit cfg a > 0
    · simp only [hd, ↓reduceIte]; exact systemAbsence_throw _
    · simp only [hd, ↓reduceIte]; exact systemAbsence_pure _

theorem systemAbsence_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).PreservesSystemAbsence := by
  unfold runReceiptAction
  exact (systemAbsence_fee _ _).bind (fun _ => (systemAbsence_checkReceiptAction _ _ _).bind
    (fun _ => applyAction_systemAbsent _ _ _))

theorem systemAbsence_runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool)
    (action : Action) (index : Nat) :
    (runReceiptActionAt c onlyAction isLast action index).PreservesSystemAbsence := by
  cases action <;> try exact systemAbsence_runReceiptAction _ _ _ _
  case functionCall method args gas deposit =>
    cases hs : actionRandomSeed c index with
    | error error =>
      simp only [runReceiptActionAt, hs]
      exact systemAbsence_throw _
    | ok seed =>
      simp only [runReceiptActionAt, hs]
      exact systemAbsence_runReceiptAction _ _ _ _

theorem systemAbsence_failureIndex (index : Option Nat) :
    (modify fun e => { e with failureIndex := index } : ExecM Unit).PreservesSystemAbsence := by
  intro before h
  exact h

theorem systemAbsence_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action)
    (index : Nat) : (runReceiptActionList c onlyAction actions index).PreservesSystemAbsence := by
  induction actions generalizing index with
  | nil => exact systemAbsence_pure _
  | cons action rest ih =>
    exact (systemAbsence_failureIndex (some index)).bind (fun _ =>
      (systemAbsence_runReceiptActionAt c onlyAction rest.isEmpty action index).bind (fun _ => ih (index + 1)))

theorem systemAbsence_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).PreservesSystemAbsence := by
  unfold receiptActionBody
  exact (systemAbsence_fee _ _).bind (fun _ => (systemAbsence_runReceiptActionList _ _ _ _).bind
    (fun _ => (systemAbsence_failureIndex none).bind (fun _ => systemAbsence_checkStorageStake _ _)))

theorem runReceiptActions_systemAbsent (c : ReceiptCtx) (st : ChainState) (h : st.SystemAccountAbsent) :
    (runReceiptActions c st).1.state.SystemAccountAbsent := by
  have hp := systemAbsence_receiptActionBody c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } h
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
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
    cases hy : action.yieldDataId with
    | some dataId =>
      rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId hr hy]
      split
      · exact h
      · exact h
    | none =>
      cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
      | false =>
        rw [processReceipt_waiting cfg ap decoder st receipt action hr hy he]
        exact h
      | true =>
        rw [processReceipt_ready cfg ap decoder st receipt action hr hy he]
        unfold processedOfExec
        split
        · exact h
        · exact applyActionReceipt_systemAbsent _ _ h
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
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
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · exact h
      · split
        · rename_i y _
          split
          · rename_i a _
            rw [runActionReceipt_eq]
            unfold processedOfExec
            split
            · exact h
            · exact applyActionReceipt_systemAbsent _ _ h
          · exact h
        · exact h
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    have hl := processDistribution_ledger cfg ap st receipt g
    unfold ChainState.ledgerState at hl
    simp only [Prod.mk.injEq] at hl
    change (processDistribution cfg ap st receipt g).state.account? systemAccount = none
    unfold ChainState.account?
    rw [hl.1]
    exact h
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
