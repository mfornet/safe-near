import NearRuntime.ActionAccountFrame
import NearRuntime.TransactionInvariants

namespace Near
open Wasm.Near

/-- The protocol's synthetic sender is not an ordinary stored account. -/
def ChainState.SystemAccountAbsent (st : ChainState) : Prop := st.account? systemAccount = none

@[simp] theorem implicitPublicKey_system : implicitPublicKey? systemAccount = none := by decide

/-- No raw action creates the reserved actor. The direct-target case uses real
creation rejection and the fact that the name is not an implicit public key. -/
-- TODO(proof): adapt the cloned proof
theorem applyAction_systemAbsent (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (hmissing : before.state.SystemAccountAbsent) :
    ((applyAction c isLast action).run.run before).2.state.SystemAccountAbsent := by
  sorry

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
-- TODO(proof): adapt the cloned proof
theorem processReceipt_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (h : st.SystemAccountAbsent) :
    (processReceipt cfg ap decoder st receipt).state.SystemAccountAbsent := by
  sorry

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
