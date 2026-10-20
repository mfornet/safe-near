import NearRuntime.AllActionFunding

namespace Near
open Wasm.Near

/-- Structural scope of the financial receipt theorem. Protocol system refunds
are constructor-shaped single transfers; ordinary receipts use ordinary actors.
This predicate assumes no financial equation and makes no validity claim beyond
these actor/action shapes. -/
def ActionReceiptFinancialShape (receipt : Receipt) (action : ActionReceipt) : Prop :=
  if receipt.predecessorId = systemAccount then ∃ amount, action.actions = [.transfer amount]
  else receipt.receiverId ≠ systemAccount ∧ action.signerId ≠ systemAccount

def ReceiptFinancialShape (receipt : Receipt) : Prop :=
  match receipt.receipt with
  | .action action => ActionReceiptFinancialShape receipt action
  | .data _ => True

/-- Net gas burn plus non-gas token destruction, such as undeliverable refunds. -/
def Exec.netTokensBurnt (exec : Exec) : Nat :=
  exec.tokensBurnt + exec.otherTokensBurnt - exec.reward

theorem applyActionReceipt_ordinary_otherBurn_zero (c : ReceiptCtx) (st : ChainState)
    (hpred : c.receipt.predecessorId ≠ systemAccount) :
    (applyActionReceipt c st).otherTokensBurnt = 0 := by
  cases he : (runReceiptActions c st).2 with
  | none =>
    have ht := congrArg (fun trace => trace.2.2.2.2.2.2)
      (finalizeReceipt_success_trace c st (runReceiptActions c st).1)
    simpa only [applyActionReceipt, Exec.commitStorage, he, Exec.finalizationTrace] using ht
  | some error =>
    have ht := congrArg (fun trace => trace.2.2.2.2.2.2)
      (finalizeReceipt_failure_trace c st (runReceiptActions c st).1 error)
    simpa [applyActionReceipt, Exec.commitStorage, he, Exec.finalizationTrace, Receipt.isRefund, hpred] using ht

/-- Successful system refunds have no VM subsidy; failure rolls it back. -/
theorem applyActionReceipt_refund_subsidy_zero (c : ReceiptCtx) (st : ChainState) (amount : Nat)
    (hpred : c.receipt.predecessorId = systemAccount) (hactions : c.action.actions = [.transfer amount]) :
    (applyActionReceipt c st).subsidizedAmount = 0 := by
  cases he : (runReceiptActions c st).2 with
  | none =>
    have hrefund : c.receipt.isRefund = true := by simp [Receipt.isRefund, hpred]
    obtain ⟨account, _, hraw⟩ := refund_success_raw c st amount hrefund hactions he
    have ht := congrArg (fun trace => trace.2.2.2.2.1)
      (finalizeReceipt_success_trace c st (runReceiptActions c st).1)
    simpa only [applyActionReceipt, Exec.commitStorage, he, Exec.finalizationTrace, hraw] using ht
  | some error =>
    have ht := congrArg (fun trace => trace.2.2.2.2.1)
      (finalizeReceipt_failure_trace c st (runReceiptActions c st).1 error)
    simpa only [applyActionReceipt, Exec.commitStorage, he, Exec.finalizationTrace] using ht

/-- Ordinary action receipts and protocol-shaped system refunds share one
closed funding law. Refund delivery failures include destroyed deposits in burn. -/
theorem applyActionReceipt_financial_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceipt : c.receipt.receipt = .action c.action)
    (hshape : ActionReceiptFinancialShape c.receipt c.action)
    (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + final.netTokensBurnt =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount := by
  by_cases hp : c.receipt.predecessorId = systemAccount
  · obtain ⟨amount, ha⟩ := (by simpa only [ActionReceiptFinancialShape, hp, ite_true] using hshape : ∃ amount, c.action.actions = [.transfer amount])
    have hf := applyActionReceipt_refund_conservation c st amount hwf hp hreceipt ha
    have hs := applyActionReceipt_refund_subsidy_zero c st amount hp ha
    dsimp only at hf ⊢
    simpa only [Exec.netTokensBurnt, hs, Nat.add_zero] using hf
  · have hs : c.receipt.receiverId ≠ systemAccount ∧ c.action.signerId ≠ systemAccount := by
      simpa only [ActionReceiptFinancialShape, hp, ite_false] using hshape
    have hf := applyActionReceipt_net_conservation c st hwf hs.1 hp hs.2 hreceipt hnew hratio
    dsimp only at hf ⊢
    simpa only [Exec.netTokensBurnt, applyActionReceipt_ordinary_otherBurn_zero c st hp, Nat.add_zero] using hf

/-- The same structural receipt scope preserves the account uniqueness needed
by subsequent execution, including refunds to missing accounts. -/
theorem applyActionReceipt_financial_accountsUnique (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hshape : ActionReceiptFinancialShape c.receipt c.action) :
    (applyActionReceipt c st).state.AccountsUnique := by
  by_cases hp : c.receipt.predecessorId = systemAccount
  · obtain ⟨amount, ha⟩ := (by simpa only [ActionReceiptFinancialShape, hp, ite_true] using hshape : ∃ amount, c.action.actions = [.transfer amount])
    unfold applyActionReceipt
    apply finalizeReceipt_accountsUnique c st _ _ hwf
    intro hsuccess
    have hrefund : c.receipt.isRefund = true := by simp [Receipt.isRefund, hp]
    obtain ⟨account, _, hraw⟩ := refund_success_raw c st amount hrefund ha hsuccess
    change (runReceiptActions c st).1.state.AccountsUnique
    rw [hraw]
    exact refundTransferState_accountsUnique c st account amount hwf
  · have hs : c.receipt.receiverId ≠ systemAccount ∧ c.action.signerId ≠ systemAccount := by
      simpa only [ActionReceiptFinancialShape, hp, ite_false] using hshape
    exact applyActionReceipt_accountsUnique c st hwf hs.1

end Near
