import NearRuntime.BalanceActionFunding
import NearRuntime.MixedFunding

namespace Near
open Wasm.Near

/-- Epoch-dependent stake/unstake never fabricates a successful state update.
The successful funding rule is vacuous because the implemented path rejects it. -/
theorem funded_stake_rejection (c : ReceiptCtx) (isLast : Bool) (stake : Nat) (pk : PublicKey) :
    (applyAction c isLast (.stake stake pk)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value _ hrun
  cases ha : before.state.account? c.receipt.receiverId with
  | none =>
    simp [-StateT.run_bind, applyAction, getAccount, getState, ha] at hrun
    have hbad := congrArg Prod.fst hrun
    cases hbad
  | some account =>
    simp [-StateT.run_bind, applyAction, getAccount, getState, ha] at hrun
    repeat' (first
      | contradiction
      | (have hbad := congrArg Prod.fst hrun; cases hbad)
      | split at hrun)

/-- Every modeled action has a concrete funding rule. Unsupported staking
cannot succeed; supported actions preserve account uniqueness and exact funding. -/
theorem funded_applyAction (c : ReceiptCtx) (isLast : Bool) (action : Action)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (applyAction c isLast action).Funded c.cfg c.action.gasPrice action.deposit := by
  cases action with
  | createAccount => exact funded_createAccount c isLast
  | deployContract code => exact funded_deployContract c isLast code
  | functionCall method args gas deposit => exact funded_functionCall c method args gas deposit isLast hreceiver
  | transfer deposit => exact funded_transfer c isLast deposit
  | stake stake pk => exact funded_stake_rejection c isLast stake pk
  | addKey pk key => exact funded_addKey c isLast pk key
  | deleteKey pk => exact funded_deleteKey c isLast pk
  | deleteAccount beneficiary => exact funded_deleteAccount c isLast beneficiary

theorem funded_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (runReceiptAction c onlyAction isLast action).Funded c.cfg c.action.gasPrice action.deposit := by
  unfold runReceiptAction
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  apply funded_bind_left_zero (funded_checkReceiptAction _ _ _)
  intro _
  exact funded_applyAction c isLast action hreceiver

theorem funded_runReceiptActionAt_all (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action)
    (index : Nat) (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (runReceiptActionAt c onlyAction isLast action index).Funded c.cfg c.action.gasPrice action.deposit := by
  cases action <;> try exact funded_runReceiptAction c onlyAction isLast _ hreceiver
  case functionCall method args gas deposit =>
    exact funded_runReceiptActionAt_functionCall c onlyAction isLast method args gas deposit index hreceiver

theorem funded_runReceiptActionList_all (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) (index : Nat)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (runReceiptActionList c onlyAction actions index).Funded c.cfg c.action.gasPrice (Fees.totalDeposit actions) := by
  induction actions generalizing index with
  | nil => exact funded_pure _ _ _
  | cons action rest ih =>
    simpa only [runReceiptActionList, Fees.totalDeposit, List.map_cons, List.sum_cons] using
      funded_bind_left_zero (funded_failureIndex _ _ (some index)) (fun _ =>
        (funded_runReceiptActionAt_all c onlyAction rest.isEmpty action index hreceiver).bind (fun _ => ih (index + 1)))

/-- Arbitrary action lists follow their real order, including creation followed
by deployment/calls, implicit creation, key changes, and final deletion. -/
theorem funded_receiptActionBody_all (c : ReceiptCtx) (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions) := by
  unfold receiptActionBody
  apply funded_bind_left_zero (funded_fee _ _ _ _)
  intro _
  exact funded_bind_right_zero (funded_runReceiptActionList_all c _ _ 0 hreceiver)
    (fun _ => funded_bind_zero (funded_failureIndex _ _ none) (fun _ => funded_checkStorageStake _ _ _))

/-- Ordinary modeled action receipts conserve funds on success and failure,
without an action-family restriction or assumed VM/ledger equations. Liquid and
locked account funds, outgoing receipt backing, net burn and explicit subsidy
are counted. This is a model theorem, not a nearcore equivalence claim. -/
theorem applyActionReceipt_net_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount :=
  applyActionReceipt_net_conservation_of_funded c st hwf hpred hsigner hreceipt hnew hratio
    (funded_receiptActionBody_all c hreceiver)

theorem Exec.creditReceiptReward_accountsUnique (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (h : exec.state.AccountsUnique) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.AccountsUnique := by
  unfold Exec.creditReceiptReward
  split
  · exact h.setAccount _ _
  · exact h

theorem addFailureData_accountsUnique (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).state.AccountsUnique ↔ exec.state.AccountsUnique := by
  unfold Exec.addFailureData
  dsimp only
  rw [failureDataFold_state]
  rfl

theorem addCompletionData_accountsUnique (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addCompletionData receiver outputs).state.AccountsUnique ↔ exec.state.AccountsUnique := by
  unfold Exec.addCompletionData
  split <;> first | rfl | (dsimp only; rw [completionDataFold_state]; rfl)

/-- Refunds, rewards and failure data preserve unique account records. On
failure only the initial state needs uniqueness because rollback discards raw effects. -/
theorem finalizeReceipt_accountsUnique (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (failed : Option RuntimeError) (hwf : st.AccountsUnique)
    (hraw : failed = none → raw.state.AccountsUnique) :
    (finalizeReceipt c st raw failed).state.AccountsUnique := by
  cases failed with
  | none =>
    have hr := hraw rfl
    unfold finalizeReceipt rollbackReceipt
    dsimp only
    repeat' (first
      | assumption
      | apply Exec.creditReceiptReward_accountsUnique
      | rw [addCompletionData_accountsUnique]
      | rw [addFailureData_accountsUnique]
      | rw [addGasRefund_accountsUnique]
      | rw [addBalanceRefund_accountsUnique]
      | split)
  | some error =>
    unfold finalizeReceipt rollbackReceipt
    dsimp only
    repeat' (first
      | assumption
      | apply Exec.creditReceiptReward_accountsUnique
      | rw [addCompletionData_accountsUnique]
      | rw [addFailureData_accountsUnique]
      | rw [addGasRefund_accountsUnique]
      | rw [addBalanceRefund_accountsUnique]
      | split)

/-- Every ordinary modeled action receipt retains the account uniqueness
premise needed by the next receipt's financial proof, on either outcome. -/
theorem applyActionReceipt_accountsUnique (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (applyActionReceipt c st).state.AccountsUnique := by
  unfold applyActionReceipt
  apply finalizeReceipt_accountsUnique c st _ _ hwf
  intro hsuccess
  exact (runReceiptActions_success_funded_of_body c st hwf (funded_receiptActionBody_all c hreceiver) hsuccess).1

end Near
