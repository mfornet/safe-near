import NearRuntime.Apply
import NearRuntime.StateInvariants

namespace Near
open Wasm.Near

def receiptsFunds (cfg : RuntimeConfig) (receipts : List Receipt) : Nat :=
  (receipts.map (Fees.receiptFunds cfg)).sum

def Exec.totalFunds (exec : Exec) (cfg : RuntimeConfig) : Nat :=
  exec.state.totalBalance + receiptsFunds cfg exec.newReceipts

@[simp] theorem receiptsFunds_append (cfg : RuntimeConfig) (xs ys : List Receipt) :
    receiptsFunds cfg (xs ++ ys) = receiptsFunds cfg xs + receiptsFunds cfg ys := by
  simp [receiptsFunds, List.map_append]

@[simp] theorem addBalanceRefund_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).totalFunds cfg = exec.totalFunds cfg + amount := by
  simp [Exec.totalFunds, Exec.addBalanceRefund, refundReceipt, ChainState.freshId,
    ChainState.totalBalance, receiptsFunds, Fees.receiptFunds, Fees.totalDeposit, Action.deposit,
    Receipt.isRefund, Nat.add_assoc]

@[simp] theorem addGasRefund_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId)
    (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).totalFunds cfg = exec.totalFunds cfg + amount := by
  simp [Exec.totalFunds, Exec.addGasRefund, gasRefundReceipt, ChainState.freshId,
    ChainState.totalBalance, receiptsFunds, Fees.receiptFunds, Fees.totalDeposit, Action.deposit,
    Receipt.isRefund, Nat.add_assoc]

theorem failureDataFold_state (receiver : AccountId) (outputs : List DataReceiver)
    (st : ChainState) (receipts : List Receipt) :
    (outputs.foldl (failureDataStep receiver) (st, receipts)).1 =
      { st with nextId := st.nextId + outputs.length } := by
  induction outputs generalizing st receipts with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons, failureDataStep, ChainState.freshId]
    rw [ih]
    simp only [List.length_cons]
    congr 1; omega

theorem failureDataFold_funds (cfg : RuntimeConfig) (receiver : AccountId) (outputs : List DataReceiver)
    (st : ChainState) (receipts : List Receipt) :
    receiptsFunds cfg (outputs.foldl (failureDataStep receiver) (st, receipts)).2 = receiptsFunds cfg receipts := by
  induction outputs generalizing st receipts with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons, failureDataStep, ChainState.freshId]
    rw [ih]
    simp [receiptsFunds, Fees.receiptFunds]

@[simp] theorem addFailureData_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId)
    (outputs : List DataReceiver) : (exec.addFailureData receiver outputs).totalFunds cfg = exec.totalFunds cfg := by
  unfold Exec.addFailureData Exec.totalFunds
  dsimp only
  rw [receiptsFunds_append, failureDataFold_state, failureDataFold_funds]
  simp [ChainState.totalBalance, receiptsFunds]

/-- Reward credit moves tokens out of gross burn, independently of the action body. -/
theorem creditReceiptReward_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (hwf : exec.state.AccountsUnique) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).totalFunds cfg =
      exec.totalFunds cfg + (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).reward := by
  unfold Exec.creditReceiptReward
  dsimp only
  split
  · rename_i account ha
    have hb := ChainState.totalBalance_setAccount exec.state receiver
      { account with amount := account.amount + exec.receiptRewardAmount cfg burnPrice purchasePrice } account hwf ha
    change (exec.state.setAccount receiver _).totalBalance + receiptsFunds cfg exec.newReceipts =
      exec.state.totalBalance + receiptsFunds cfg exec.newReceipts + _
    dsimp only at hb ⊢
    omega
  · rfl

/-- Rollback erases all tentative action effects, promises and subsidies. -/
theorem rollbackReceipt_failure (st : ChainState) (exec : Exec) (err : RuntimeError) :
    (rollbackReceipt st exec (some err)).state = st ∧
    (rollbackReceipt st exec (some err)).newReceipts = [] ∧
    (rollbackReceipt st exec (some err)).subsidizedAmount = 0 ∧
    (rollbackReceipt st exec (some err)).gasUsed = exec.gasBurnt ∧
    (rollbackReceipt st exec (some err)).gasBurnt = exec.gasBurnt ∧
    (rollbackReceipt st exec (some err)).logs = exec.logs ∧
    (rollbackReceipt st exec (some err)).result = some (.failure err) := by
  simp [rollbackReceipt]

@[simp] theorem addBalanceRefund_accountsUnique (exec : Exec) (receiver : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).state.AccountsUnique ↔ exec.state.AccountsUnique := by
  rfl

@[simp] theorem addGasRefund_accountsUnique (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).state.AccountsUnique ↔ exec.state.AccountsUnique := by
  rfl

/-- Ordinary failure finalization accounts for the entire deposit and gas refund.
The gas-settlement equation is kept separate from this structural accounting lemma. -/
theorem finalizeReceipt_failure_funds (c : ReceiptCtx) (st : ChainState) (raw : Exec) (err : RuntimeError)
    (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hsigner : c.action.signerId ≠ systemAccount) :
    let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
    let final := finalizeReceipt c st raw (some err)
    final.totalFunds c.cfg = st.totalBalance + Fees.totalDeposit c.action.actions +
      settlement.refund + final.reward := by
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
  let base := { rollbackReceipt st raw (some err) with
    tokensBurnt := settlement.tokensBurnt, otherTokensBurnt := 0 }
  let deposit := if Fees.totalDeposit c.action.actions > 0 then
    base.addBalanceRefund c.receipt.predecessorId (Fees.totalDeposit c.action.actions) else base
  let gas := if settlement.refund > 0 then
    deposit.addGasRefund c.action.signerId c.action.signerPublicKey settlement.refund else deposit
  have hbase : base.totalFunds c.cfg = st.totalBalance := by
    simp [base, rollbackReceipt, Exec.totalFunds, receiptsFunds]
  have hd : deposit.totalFunds c.cfg = st.totalBalance + Fees.totalDeposit c.action.actions := by
    dsimp only [deposit]
    split
    · rw [addBalanceRefund_totalFunds, hbase]
    · rename_i h
      have hz : Fees.totalDeposit c.action.actions = 0 := by omega
      simp [hz, hbase]
  have hg : gas.totalFunds c.cfg = st.totalBalance + Fees.totalDeposit c.action.actions + settlement.refund := by
    dsimp only [gas]
    split
    · rw [addGasRefund_totalFunds, hd]
    · rename_i h
      have hz : settlement.refund = 0 := by omega
      simp [hz, hd]
  have hgu : gas.state.AccountsUnique := by
    dsimp only [gas, deposit]
    split <;> split <;> simpa [base, rollbackReceipt] using hwf
  have hr := creditReceiptReward_totalFunds c.cfg gas c.receipt.receiverId
    settlement.burnPrice c.action.gasPrice hgu
  rw [hg] at hr
  have hrefund : c.receipt.isRefund = false := by simp [Receipt.isRefund, hpred]
  let rewarded := gas.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let data := rewarded.addFailureData c.receipt.receiverId c.action.outputDataReceivers
  have hf : finalizeReceipt c st raw (some err) =
      { data with result := some (data.result.getD (.successValue [])) } := by
    simp [finalizeReceipt, hrefund, rollbackReceipt, hpred, hsigner,
      base, deposit, gas, settlement, data, rewarded]
  dsimp only
  rw [hf]
  change data.totalFunds c.cfg = _ + rewarded.reward
  change (rewarded.addFailureData c.receipt.receiverId c.action.outputDataReceivers).totalFunds c.cfg = _
  rw [addFailureData_totalFunds]
  exact hr

/-- Failed ordinary receipt conservation, including in-flight refund backing.
The action body's burnt gas must fit the incoming purchased budget. Rewards are
shown separately from gross burn; this theorem does not assume a reward bound. -/
theorem finalizeReceipt_failure_conservation (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hwf : st.AccountsUnique)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hgas : raw.gasBurnt ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) :
    let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
    let final := finalizeReceipt c st raw (some err)
    final.totalFunds c.cfg + settlement.tokensBurnt =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.reward := by
  have hf := finalizeReceipt_failure_funds c st raw err hwf hpred hsigner
  have hg := Fees.settleGas_conservation c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt
    false hnew hgas (Nat.le_refl _)
  have hi : Fees.receiptFunds c.cfg c.receipt = Fees.totalDeposit c.action.actions +
      Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions * c.action.gasPrice := by
    simp [Fees.receiptFunds, hreceipt, Receipt.isRefund, hpred]
  dsimp only at hf ⊢
  rw [hi]
  simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at hg
  omega

/-- Connect the failed-receipt accounting theorem to the executable action path. -/
theorem applyActionReceipt_failure_conservation (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hrun : runReceiptActions c st = (raw, some err))
    (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hsigner : c.action.signerId ≠ systemAccount) (hreceipt : c.receipt.receipt = .action c.action)
    (hnew : c.cfg.accountCostIncrease = true)
    (hgas : raw.gasBurnt ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) :
    let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
    (applyActionReceipt c st).totalFunds c.cfg + settlement.tokensBurnt =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + (applyActionReceipt c st).reward := by
  simpa only [applyActionReceipt, hrun] using
    finalizeReceipt_failure_conservation c st raw err hwf hpred hsigner hreceipt hnew hgas

end Near
