import NearRuntime.BlockConservation

namespace Near
open Wasm.Near

/-- No raw action can succeed against the absent reserved receiver. In
particular creation cannot install the actor before a later function call. -/
theorem applyAction_system_no_success (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (hreceiver : c.receipt.receiverId = systemAccount) (hmissing : before.state.SystemAccountAbsent) :
    ((applyAction c isLast action).run.run before).1 ≠ .ok () := by
  have hn : before.state.account? systemAccount = none := hmissing
  cases action with
  | createAccount =>
    rw [applyCreateAccount_system_missing c isLast before hreceiver hn]
    intro he; cases he
  | deployContract code => rw [applyDeployContract_run]; simp [hreceiver, hn]
  | functionCall method args gas deposit =>
    rw [show applyAction c isLast (.functionCall method args gas deposit) =
      applyFunctionCall c method args gas deposit isLast from rfl, applyFunctionCall_run]
    simp [hreceiver, hn]
  | transfer amount =>
    rw [applyTransfer_run]
    simp only [hreceiver, hn, implicitPublicKey_system]
    split <;> simp
  | stake amount pk =>
    simp [-ExceptT.run_bind, -StateT.run_bind, applyAction, getAccount, getState, hreceiver, hn]
  | addKey pk key =>
    rw [applyAddKey_run]
    simp only [hreceiver, hn]
    split <;> simp
  | deleteKey pk =>
    rw [applyDeleteKey_run]
    simp only [hreceiver, hn]
    split <;> simp
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    simp only [hreceiver, hn]
    split <;> simp

/-- A rejection rule used only for operations targeting the reserved receiver. -/
def ExecM.RejectsAbsentSystem (operation : ExecM Unit) : Prop :=
  ∀ before, before.state.SystemAccountAbsent → (operation.run.run before).1 ≠ .ok ()

theorem rejectsAbsentSystem_bind_right {operation : ExecM α} {next : α → ExecM Unit}
    (hfirst : operation.PreservesSystemAbsence) (hnext : ∀ value, (next value).RejectsAbsentSystem) :
    (operation >>= next).RejectsAbsentSystem := by
  intro before hmissing
  rw [execM_run_bind]
  have hp := hfirst before hmissing
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => intro hsuccess; cases hsuccess
    | ok value => exact hnext value middle hp

theorem rejectsAbsentSystem_bind_left {operation : ExecM Unit} {next : Unit → ExecM Unit}
    (hfirst : operation.RejectsAbsentSystem) : (operation >>= next).RejectsAbsentSystem := by
  intro before hmissing
  rw [execM_run_bind]
  have hn := hfirst before hmissing
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hn
    cases result with
    | error error => intro hsuccess; cases hsuccess
    | ok value => cases value; exact False.elim (hn rfl)

theorem runReceiptAction_system_no_success (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action)
    (hreceiver : c.receipt.receiverId = systemAccount) :
    (runReceiptAction c onlyAction isLast action).RejectsAbsentSystem := by
  unfold runReceiptAction
  apply rejectsAbsentSystem_bind_right (systemAbsence_fee _ _)
  intro _
  apply rejectsAbsentSystem_bind_right (systemAbsence_checkReceiptAction _ _ _)
  intro _ before hmissing
  exact applyAction_system_no_success c isLast action before hreceiver hmissing

theorem receiptActionBody_system_nonempty_no_success (c : ReceiptCtx)
    (hreceiver : c.receipt.receiverId = systemAccount) (hnonempty : c.action.actions ≠ []) :
    (receiptActionBody c).RejectsAbsentSystem := by
  cases ha : c.action.actions with
  | nil => exact False.elim (hnonempty ha)
  | cons action rest =>
    unfold receiptActionBody
    apply rejectsAbsentSystem_bind_right (systemAbsence_fee _ _)
    intro _
    apply rejectsAbsentSystem_bind_left
    rw [ha, runReceiptActionList]
    exact rejectsAbsentSystem_bind_left (runReceiptAction_system_no_success c _ _ action hreceiver)

/-- Nonempty receipts targeting the absent synthetic actor fail before any
later action can execute. The failure is derived from the real action body. -/
theorem runReceiptActions_system_nonempty_failed (c : ReceiptCtx) (st : ChainState)
    (hreceiver : c.receipt.receiverId = systemAccount) (hmissing : st.SystemAccountAbsent)
    (hnonempty : c.action.actions ≠ []) : (runReceiptActions c st).2 ≠ none := by
  have hn := receiptActionBody_system_nonempty_no_success c hreceiver hnonempty
    { state := st, actorId := c.receipt.predecessorId } hmissing
  unfold runReceiptActions
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId } with
  | mk result raw =>
    rw [he] at hn
    cases result with
    | error error => simp [he]
    | ok value => cases value; exact False.elim (hn rfl)

/-- Empty action lists still pay receipt fees, but require no VM funding rule. -/
theorem funded_receiptActionBody_empty (c : ReceiptCtx) (hempty : c.action.actions = []) :
    (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions) := by
  have hz : Fees.totalDeposit c.action.actions = 0 := by simp [hempty, Fees.totalDeposit]
  rw [hz]
  unfold receiptActionBody
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  rw [hempty, runReceiptActionList]
  exact funded_bind_right_zero (funded_pure _ _ _) (fun _ => funded_checkStorageStake _ _ _)

/-- Ordinary reserved-target receipts conserve funds through their actual
failure/empty-action path, rather than being excluded by receiver scope. -/
theorem applyActionReceipt_system_target_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent)
    (hreceiver : c.receipt.receiverId = systemAccount) (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hsigner : c.action.signerId ≠ systemAccount) (hreceipt : c.receipt.receipt = .action c.action)
    (hnew : c.cfg.accountCostIncrease = true) (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount := by
  by_cases hempty : c.action.actions = []
  · exact applyActionReceipt_net_conservation_of_funded c st hwf hpred hsigner hreceipt hnew hratio
      (funded_receiptActionBody_empty c hempty)
  · have hn := runReceiptActions_system_nonempty_failed c st hreceiver hmissing hempty
    cases he : (runReceiptActions c st).2 with
    | none => exact False.elim (hn he)
    | some error =>
      have hf := applyActionReceipt_failed_net_conservation c st error he hwf hpred hsigner hreceipt hnew hratio
      have ht := congrArg (fun trace => trace.2.2.2.2.1)
        (finalizeReceipt_failure_trace c st (runReceiptActions c st).1 error)
      have hs : (applyActionReceipt c st).subsidizedAmount = 0 := by
        simpa only [applyActionReceipt, he, Exec.finalizationTrace] using ht
      dsimp only at hf ⊢
      rw [hs, Nat.add_zero]
      exact hf

theorem applyActionReceipt_system_target_accountsUnique (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent)
    (hreceiver : c.receipt.receiverId = systemAccount) : (applyActionReceipt c st).state.AccountsUnique := by
  unfold applyActionReceipt
  apply finalizeReceipt_accountsUnique c st _ _ hwf
  intro hsuccess
  by_cases hempty : c.action.actions = []
  · exact (runReceiptActions_success_funded_of_body c st hwf (funded_receiptActionBody_empty c hempty) hsuccess).1
  · exact False.elim (runReceiptActions_system_nonempty_failed c st hreceiver hmissing hempty hsuccess)

/-- Account uniqueness is available for any target when the reserved actor is
absent; the target name need not be excluded from the receipt interface. -/
theorem applyActionReceipt_accountsUnique_of_systemAbsent (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) : (applyActionReceipt c st).state.AccountsUnique := by
  by_cases hreceiver : c.receipt.receiverId = systemAccount
  · exact applyActionReceipt_system_target_accountsUnique c st hwf hmissing hreceiver
  · exact applyActionReceipt_accountsUnique c st hwf hreceiver

end Near
