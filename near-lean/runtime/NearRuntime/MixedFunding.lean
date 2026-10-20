import NearRuntime.MetadataFunding
import NearRuntime.ReceiptFunding

namespace Near
open Wasm.Near

/-- Incoming action families with concrete funding rules. Creation, transfers,
stake and account deletion still require their own action-family proofs. -/
def MixedFundingAction : Action → Prop
  | .deployContract .. | .functionCall .. | .addKey .. | .deleteKey .. => True
  | _ => False

/-- The action implementation, not a supplied ledger equation, discharges the
funding rule for every included constructor. -/
theorem funded_mixed_action (c : ReceiptCtx) (isLast : Bool) (action : Action)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) (h : MixedFundingAction action) :
    (applyAction c isLast action).Funded c.cfg c.action.gasPrice action.deposit := by
  cases action with
  | deployContract code => exact funded_deployContract c isLast code
  | functionCall method args gas deposit => exact funded_functionCall c method args gas deposit isLast hreceiver
  | addKey pk key => exact funded_addKey c isLast pk key
  | deleteKey pk => exact funded_deleteKey c isLast pk
  | _ => contradiction

theorem funded_runReceiptAction_mixed (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) (h : MixedFundingAction action) :
    (runReceiptAction c onlyAction isLast action).Funded c.cfg c.action.gasPrice action.deposit := by
  unfold runReceiptAction
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  apply funded_bind_left_zero (funded_checkReceiptAction _ _ _)
  intro _
  exact funded_mixed_action c isLast action hreceiver h

theorem funded_runReceiptActionAt_mixed (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action)
    (index : Nat) (hreceiver : c.receipt.receiverId ≠ systemAccount) (h : MixedFundingAction action) :
    (runReceiptActionAt c onlyAction isLast action index).Funded c.cfg c.action.gasPrice action.deposit := by
  cases action <;> try exact funded_runReceiptAction_mixed c onlyAction isLast _ hreceiver h
  case functionCall method args gas deposit =>
    exact funded_runReceiptActionAt_functionCall c onlyAction isLast method args gas deposit index hreceiver

theorem funded_runReceiptActionList_mixed (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) (index : Nat)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) (h : ∀ action ∈ actions, MixedFundingAction action) :
    (runReceiptActionList c onlyAction actions index).Funded c.cfg c.action.gasPrice (Fees.totalDeposit actions) := by
  induction actions generalizing index with
  | nil => exact funded_pure _ _ _
  | cons action rest ih =>
    have ha := h action (by simp)
    have hr := ih (index + 1) (by intro a hm; exact h a (by simp [hm]))
    simpa only [runReceiptActionList, Fees.totalDeposit, List.map_cons, List.sum_cons] using
      funded_bind_left_zero (funded_failureIndex _ _ (some index)) (fun _ =>
        (funded_runReceiptActionAt_mixed c onlyAction rest.isEmpty action index hreceiver ha).bind (fun _ => hr))

/-- This follows the actual action order and state changes. Calls following a
deployment use the newly installed code; key updates and storage checks are
retained and may fail, causing ordinary receipt rollback. -/
theorem funded_receiptActionBody_mixed (c : ReceiptCtx) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (h : ∀ action ∈ c.action.actions, MixedFundingAction action) :
    (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions) := by
  unfold receiptActionBody
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  exact funded_bind_right_zero (funded_runReceiptActionList_mixed c _ _ 0 hreceiver h)
    (fun _ => funded_bind_zero (funded_failureIndex _ _ none) (fun _ => funded_checkStorageStake _ _ _))

/-- Complete net settlement conservation for arbitrary ordered mixtures of
calls, deployment and key changes, on success and failure. Structural and
protocol premises remain explicit; no financial or VM-output oracle is assumed. -/
theorem applyActionReceipt_mixed_net_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hactions : ∀ action ∈ c.action.actions, MixedFundingAction action) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount :=
  applyActionReceipt_net_conservation_of_funded c st hwf hpred hsigner hreceipt hnew hratio
    (funded_receiptActionBody_mixed c hreceiver hactions)

end Near
