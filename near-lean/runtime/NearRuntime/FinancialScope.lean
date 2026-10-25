import NearRuntime.ReservedTargetFunding

namespace Near
open Wasm.Near

/-- Financial actor scope allowing arbitrary receivers. System-origin receipts
must be canonical single-transfer refunds; ordinary signers are not synthetic.
Conservation under this scope additionally requires an absent stored system actor. -/
def ActionReceiptFinancialScope (receipt : Receipt) (action : ActionReceipt) : Prop :=
  if receipt.predecessorId = systemAccount then ∃ amount, action.actions = [.transfer amount]
  else action.signerId ≠ systemAccount

def ReceiptFinancialScope (receipt : Receipt) : Prop :=
  match receipt.receipt with
  | .action action => ActionReceiptFinancialScope receipt action
  | .data _ | .globalDistribution _ => True

theorem ActionReceiptFinancialShape.to_scope (receipt : Receipt) (action : ActionReceipt)
    (h : ActionReceiptFinancialShape receipt action) : ActionReceiptFinancialScope receipt action := by
  by_cases hp : receipt.predecessorId = systemAccount
  · simpa only [ActionReceiptFinancialShape, ActionReceiptFinancialScope, hp, ite_true] using h
  · have hs : receipt.receiverId ≠ systemAccount ∧ action.signerId ≠ systemAccount := by
      simpa only [ActionReceiptFinancialShape, hp, ite_false] using h
    simpa only [ActionReceiptFinancialScope, hp, ite_false] using hs.2

theorem ReceiptFinancialShape.to_scope (receipt : Receipt) (h : ReceiptFinancialShape receipt) :
    ReceiptFinancialScope receipt := by
  cases hr : receipt.receipt with
  | data data => simp only [ReceiptFinancialScope, hr]
  | globalDistribution g => simp only [ReceiptFinancialScope, hr]
  | action action =>
    have ha : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, hr] using h
    simpa only [ReceiptFinancialScope, hr] using ActionReceiptFinancialShape.to_scope receipt action ha

/-- Ordinary reserved targets are covered through their real failure or empty
path; no receiver-name exclusion remains in this local financial interface. -/
theorem applyActionReceipt_scope_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent)
    (hreceipt : c.receipt.receipt = .action c.action) (hscope : ActionReceiptFinancialScope c.receipt c.action)
    (hnew : c.cfg.accountCostIncrease = true) (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + final.netTokensBurnt =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount := by
  by_cases hp : c.receipt.predecessorId = systemAccount
  · have hs : ActionReceiptFinancialShape c.receipt c.action := by
      simpa only [ActionReceiptFinancialShape, ActionReceiptFinancialScope, hp, ite_true] using hscope
    exact applyActionReceipt_financial_conservation c st hwf hreceipt hs hnew hratio
  · have hsigner : c.action.signerId ≠ systemAccount := by
      simpa only [ActionReceiptFinancialScope, hp, ite_false] using hscope
    by_cases hr : c.receipt.receiverId = systemAccount
    · have hf := applyActionReceipt_system_target_conservation c st hwf hmissing hr hp hsigner hreceipt hnew hratio
      dsimp only [Exec.netTokensBurnt]
      rw [applyActionReceipt_ordinary_otherBurn_zero c st hp, Nat.add_zero]
      exact hf
    · have hs : ActionReceiptFinancialShape c.receipt c.action := by
        simpa only [ActionReceiptFinancialShape, hp, ite_false] using And.intro hr hsigner
      exact applyActionReceipt_financial_conservation c st hwf hreceipt hs hnew hratio

/-- Reward backing also extends to the broader actor scope. -/
theorem applyActionReceipt_scope_reward_backed (c : ReceiptCtx) (st : ChainState)
    (hscope : ActionReceiptFinancialScope c.receipt c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    (applyActionReceipt c st).reward ≤ (applyActionReceipt c st).tokensBurnt := by
  by_cases hp : c.receipt.predecessorId = systemAccount
  · have hs : ActionReceiptFinancialShape c.receipt c.action := by
      simpa only [ActionReceiptFinancialShape, ActionReceiptFinancialScope, hp, ite_true] using hscope
    exact applyActionReceipt_reward_backed c st hs hnew hratio
  · cases he : (runReceiptActions c st).2 with
    | none => exact applyActionReceipt_success_reward_backed c st hp hnew hratio he
    | some error =>
      have hb := finalizeReceipt_failure_reward_le_burn c st (runReceiptActions c st).1 error
        hnew hratio (runReceiptActions_gas_bounds c st).1
      have ht := finalizeReceipt_failure_tokensBurnt c st (runReceiptActions c st).1 error hp
      simpa only [applyActionReceipt, Exec.commitStorage, he, ht] using hb

theorem emitFunctionCallData_financialScope (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (receipts : List Receipt) (h : ∀ receipt ∈ receipts, ReceiptFinancialScope receipt) :
    ∀ receipt ∈ (emitFunctionCallData receiver bytes outputs initial receipts).2, ReceiptFinancialScope receipt := by
  simp only [emitFunctionCallData, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  apply foldl_preserves (fun pair : ChainState × List Receipt => ∀ receipt ∈ pair.2, ReceiptFinancialScope receipt) _ _ _ _ h
  intro pair output hp receipt hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact hp receipt hold
  · have he := List.mem_singleton.mp hnew
    subst receipt
    trivial

theorem emitFunctionCallActions_financialScope (c : ReceiptCtx) (specs : List ReceiptSpec)
    (ids : Array ReceiptId) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (receipts : List Receipt) (hsender : c.receipt.receiverId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (h : ∀ receipt ∈ receipts, ReceiptFinancialScope receipt) :
    ∀ receipt ∈ emitFunctionCallActions c specs ids outputs inputs receipts, ReceiptFinancialScope receipt := by
  simp only [emitFunctionCallActions, Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl]
  apply foldl_preserves (fun receipts : List Receipt => ∀ receipt ∈ receipts, ReceiptFinancialScope receipt) _ _ _ _ h
  intro receipts index hp receipt hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact hp receipt hold
  · have he := List.mem_singleton.mp hnew
    subst receipt
    simpa only [ReceiptFinancialScope, ActionReceiptFinancialScope, hsender, ite_false] using hsigner

/-- VM promises may target the reserved name while retaining financial actor
scope. A real successful call's sender is ordinary when the system actor is absent. -/
theorem materializeFunctionCall_financialScope (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (hsender : c.receipt.receiverId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount) :
    ∀ receipt ∈ (materializeFunctionCallRaw c isLast outcome initial).receipts, ReceiptFinancialScope receipt := by
  rw [materializeFunctionCallRaw_eq_stages]
  cases hr : outcome.returnData <;> dsimp only
  all_goals apply emitFunctionCallActions_financialScope _ _ _ _ _ _ hsender hsigner
  all_goals simp

end Near
