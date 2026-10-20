import NearRuntime.GasInvariants
import NearRuntime.StateInvariants

namespace Near
open Wasm.Near

def receiptsFunds (cfg : RuntimeConfig) (receipts : List Receipt) : Nat :=
  (receipts.map (Fees.receiptFunds cfg)).sum

def Exec.totalFunds (exec : Exec) (cfg : RuntimeConfig) : Nat :=
  exec.state.totalBalance + receiptsFunds cfg exec.newReceipts

@[simp] theorem Exec.totalFunds_storageAccounting (exec : Exec) (cfg : RuntimeConfig)
    (accounting : Option TrieOverlay.State) :
    ({ exec with storageAccounting := accounting } : Exec).totalFunds cfg = exec.totalFunds cfg := rfl

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

theorem successDataFold_state (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (st : ChainState) (receipts : List Receipt) :
    (outputs.foldl (successDataStep receiver bytes) (st, receipts)).1 =
      { st with nextId := st.nextId + outputs.length } := by
  induction outputs generalizing st receipts with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons, successDataStep, ChainState.freshId]
    rw [ih]
    simp only [List.length_cons]
    congr 1; omega

theorem successDataFold_funds (cfg : RuntimeConfig) (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (st : ChainState) (receipts : List Receipt) :
    receiptsFunds cfg (outputs.foldl (successDataStep receiver bytes) (st, receipts)).2 = receiptsFunds cfg receipts := by
  induction outputs generalizing st receipts with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons, successDataStep, ChainState.freshId]
    rw [ih]
    simp [receiptsFunds, Fees.receiptFunds]

@[simp] theorem addSuccessData_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId)
    (outputs : List DataReceiver) (bytes : Bytes) : (exec.addSuccessData receiver outputs bytes).totalFunds cfg = exec.totalFunds cfg := by
  unfold Exec.addSuccessData Exec.totalFunds
  dsimp only
  rw [receiptsFunds_append, successDataFold_state, successDataFold_funds]
  simp [ChainState.totalBalance, receiptsFunds]

@[simp] theorem forwardResult_receiptFunds (cfg : RuntimeConfig) (receipt : Receipt)
    (target : ReceiptId) (outputs : List DataReceiver) :
    Fees.receiptFunds cfg (receipt.forwardResult target outputs) = Fees.receiptFunds cfg receipt := by
  unfold Receipt.forwardResult
  split
  · cases h : receipt.receipt <;> simp [Fees.receiptFunds, h, Receipt.isRefund, Fees.receiptGasBudget]
  · rfl

@[simp] theorem forwardResult_totalFunds (cfg : RuntimeConfig) (exec : Exec) (target : ReceiptId)
    (outputs : List DataReceiver) : (exec.forwardResult target outputs).totalFunds cfg = exec.totalFunds cfg := by
  simp [Exec.totalFunds, Exec.forwardResult, receiptsFunds, List.map_map, Function.comp_def]

@[simp] theorem deliverResult_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId)
    (outputs : List DataReceiver) : (exec.deliverResult receiver outputs).totalFunds cfg = exec.totalFunds cfg := by
  unfold Exec.deliverResult
  split <;> simp

@[simp] theorem finishReceiptResult_totalFunds (cfg : RuntimeConfig) (exec : Exec) (c : ReceiptCtx)
    (failed : Option RuntimeError) : (exec.finishReceiptResult c failed).totalFunds cfg = exec.totalFunds cfg := by
  unfold Exec.finishReceiptResult
  rw [deliverResult_totalFunds]
  split <;> rfl

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

/-- Observations untouched by refund, reward and failure-data production. -/
def Exec.finalizationTrace (exec : Exec) : Nat × Nat × Nat × List String × Nat × Nat × Nat :=
  (exec.gasBurnt, exec.gasUsed, exec.gasBurntForFunctionCall, exec.logs,
    exec.subsidizedAmount, exec.tokensBurnt, exec.otherTokensBurnt)

@[simp] theorem ite_trace (p : Prop) [Decidable p] (yes no : Exec) :
    (if p then yes else no).finalizationTrace =
      if p then yes.finalizationTrace else no.finalizationTrace := by split <;> rfl

@[simp] theorem ite_result (p : Prop) [Decidable p] (yes no : Exec) :
    (if p then yes else no).result = if p then yes.result else no.result := by split <;> rfl

@[simp] theorem addBalanceRefund_trace (exec : Exec) (receiver : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).finalizationTrace = exec.finalizationTrace := rfl

@[simp] theorem addGasRefund_trace (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).finalizationTrace = exec.finalizationTrace := rfl

@[simp] theorem addFailureData_trace (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).finalizationTrace = exec.finalizationTrace := rfl

@[simp] theorem creditReceiptReward_trace (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).finalizationTrace = exec.finalizationTrace := by
  unfold Exec.creditReceiptReward
  split <;> rfl

@[simp] theorem setResult_trace (exec : Exec) (result : Option ExecutionStatus) :
    ({ exec with result := result } : Exec).finalizationTrace = exec.finalizationTrace := rfl

@[simp] theorem addBalanceRefund_result (exec : Exec) (receiver : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).result = exec.result := rfl

@[simp] theorem addGasRefund_result (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).result = exec.result := rfl

@[simp] theorem addFailureData_result (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).result = exec.result := rfl

@[simp] theorem creditReceiptReward_result (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).result = exec.result := by
  unfold Exec.creditReceiptReward
  split <;> rfl

@[simp] theorem deliverResult_trace (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.deliverResult receiver outputs).finalizationTrace = exec.finalizationTrace := by
  unfold Exec.deliverResult
  split <;> rfl

@[simp] theorem deliverResult_result (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.deliverResult receiver outputs).result = exec.result := by
  unfold Exec.deliverResult
  split <;> rfl

@[simp] theorem deliverResult_reward (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.deliverResult receiver outputs).reward = exec.reward := by
  unfold Exec.deliverResult
  split <;> rfl

@[simp] theorem finishReceiptResult_trace (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) :
    (exec.finishReceiptResult c failed).finalizationTrace = exec.finalizationTrace := by
  unfold Exec.finishReceiptResult
  rw [deliverResult_trace]
  split <;> rfl

@[simp] theorem finishReceiptResult_reward (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) :
    (exec.finishReceiptResult c failed).reward = exec.reward := by
  unfold Exec.finishReceiptResult
  rw [deliverResult_reward]
  split <;> rfl

@[simp] theorem finishReceiptResult_failure_result (exec : Exec) (c : ReceiptCtx) (error : RuntimeError) :
    (exec.finishReceiptResult c (some error)).result = exec.result := by
  simp [Exec.finishReceiptResult]

@[simp] theorem deliverResult_account (exec : Exec) (receiver id : AccountId) (outputs : List DataReceiver) :
    (exec.deliverResult receiver outputs).state.account? id = exec.state.account? id := by
  unfold Exec.deliverResult
  split
  · simp only [Exec.addSuccessData, successDataFold_state]
    rfl
  · simp only [Exec.addFailureData, failureDataFold_state]
    rfl
  · rfl

@[simp] theorem finishReceiptResult_account (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) (id : AccountId) :
    (exec.finishReceiptResult c failed).state.account? id = exec.state.account? id := by
  unfold Exec.finishReceiptResult
  rw [deliverResult_account]
  split <;> rfl

@[simp] theorem finishReceiptResult_rewardAmount (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError)
    (cfg : RuntimeConfig) (burnPrice purchasePrice : Nat) :
    (exec.finishReceiptResult c failed).receiptRewardAmount cfg burnPrice purchasePrice =
      exec.receiptRewardAmount cfg burnPrice purchasePrice := by
  unfold Exec.finishReceiptResult
  split
  · rfl
  · dsimp only
    unfold Exec.deliverResult
    split <;> rfl

/-- Logs and gas survive receipt failure; subsidy is rolled back and gross burn
is exactly the settlement burn exposed by the executable result. -/
theorem finalizeReceipt_failure_trace (c : ReceiptCtx) (st : ChainState) (raw : Exec) (err : RuntimeError) :
    let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
    (finalizeReceipt c st raw (some err)).finalizationTrace =
      (raw.gasBurnt, raw.gasBurnt, raw.gasBurntForFunctionCall, raw.logs, 0,
        if c.receipt.isRefund then 0 else settlement.tokensBurnt,
        if c.receipt.isRefund then Fees.totalDeposit c.action.actions else 0) := by
  unfold finalizeReceipt
  simp only [setResult_trace, finishReceiptResult_trace, creditReceiptReward_trace,
    ite_trace, addBalanceRefund_trace, addGasRefund_trace, ite_self]
  simp [rollbackReceipt, Exec.finalizationTrace]

@[simp] theorem finalizeReceipt_failure_result (c : ReceiptCtx) (st : ChainState) (raw : Exec) (err : RuntimeError) :
    (finalizeReceipt c st raw (some err)).result = some (.failure err) := by
  unfold finalizeReceipt
  simp [rollbackReceipt, Exec.finishReceiptResult, Exec.deliverResult]

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
    simp [finalizeReceipt, Exec.finishReceiptResult, Exec.deliverResult, hrefund, rollbackReceipt, hpred, hsigner,
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
  simpa only [applyActionReceipt, Exec.commitStorage, hrun, Exec.totalFunds_storageAccounting] using
    finalizeReceipt_failure_conservation c st raw err hwf hpred hsigner hreceipt hnew hgas

/-- A configured reward fraction at most one cannot exceed burnt function-call
funds. Division by zero also satisfies this bound under Lean's Nat semantics. -/
theorem receiptRewardAmount_le (exec : Exec) (cfg : RuntimeConfig) (burnPrice purchasePrice : Nat)
    (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hfc : exec.gasBurntForFunctionCall ≤ exec.gasBurnt) :
    exec.receiptRewardAmount cfg burnPrice purchasePrice ≤ exec.gasBurnt * burnPrice := by
  have hd : exec.gasBurntForFunctionCall * cfg.fees.burntGasReward.1 / cfg.fees.burntGasReward.2 ≤
      exec.gasBurntForFunctionCall :=
    Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using (Nat.mul_le_mul_left exec.gasBurntForFunctionCall hratio))
  simpa [Exec.receiptRewardAmount, hnew] using Nat.mul_le_mul_right burnPrice (hd.trans hfc)

/-- Gross v85+ burn includes the function execution burn before penalties. -/
theorem settlement_burn_lower_bound (cfg : RuntimeConfig) (purchase current prepaid used burnt : Nat)
    (hnew : cfg.accountCostIncrease = true) :
    burnt * (Fees.settleGas cfg purchase current prepaid used burnt false).burnPrice ≤
      (Fees.settleGas cfg purchase current prepaid used burnt false).tokensBurnt := by
  have hd : min purchase current - purchase = 0 := Nat.sub_eq_zero_of_le (Nat.min_le_left _ _)
  simp [Fees.settleGas, hnew, hd]

@[simp] theorem addFailureData_reward (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).reward = exec.reward := rfl

@[simp] theorem ite_rewardAmount (p : Prop) [Decidable p] (yes no : Exec)
    (cfg : RuntimeConfig) (burnPrice purchasePrice : Nat) :
    (if p then yes else no).receiptRewardAmount cfg burnPrice purchasePrice =
      if p then yes.receiptRewardAmount cfg burnPrice purchasePrice else
        no.receiptRewardAmount cfg burnPrice purchasePrice := by split <;> rfl

@[simp] theorem addBalanceRefund_rewardAmount (exec : Exec) (receiver : AccountId) (amount : Nat)
    (cfg : RuntimeConfig) (burnPrice purchasePrice : Nat) :
    (exec.addBalanceRefund receiver amount).receiptRewardAmount cfg burnPrice purchasePrice =
      exec.receiptRewardAmount cfg burnPrice purchasePrice := rfl

@[simp] theorem addGasRefund_rewardAmount (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat)
    (cfg : RuntimeConfig) (burnPrice purchasePrice : Nat) :
    (exec.addGasRefund receiver pk amount).receiptRewardAmount cfg burnPrice purchasePrice =
      exec.receiptRewardAmount cfg burnPrice purchasePrice := rfl

theorem creditReceiptReward_reward_le (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).reward ≤
      exec.receiptRewardAmount cfg burnPrice purchasePrice := by
  unfold Exec.creditReceiptReward
  split <;> simp

/-- Failed execution can credit only its attempted function-call reward. -/
theorem finalizeReceipt_failure_reward_le (c : ReceiptCtx) (st : ChainState) (raw : Exec) (err : RuntimeError) :
    let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
    (finalizeReceipt c st raw (some err)).reward ≤
      raw.receiptRewardAmount c.cfg settlement.burnPrice c.action.gasPrice := by
  unfold finalizeReceipt
  dsimp only
  simp only [Option.isSome, ite_true, finishReceiptResult_reward]
  apply (creditReceiptReward_reward_le _ _ _ _ _).trans
  simp only [ite_rewardAmount, addGasRefund_rewardAmount, addBalanceRefund_rewardAmount, ite_self]
  rfl

/-- Receiver rewards cannot exceed gross burn when the configured fraction and
function-call gas satisfy their respective bounds. -/
theorem finalizeReceipt_failure_reward_le_burn (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hfc : raw.gasBurntForFunctionCall ≤ raw.gasBurnt) :
    let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
    (finalizeReceipt c st raw (some err)).reward ≤ settlement.tokensBurnt := by
  exact (finalizeReceipt_failure_reward_le c st raw err).trans
    ((receiptRewardAmount_le raw c.cfg _ _ hnew hratio hfc).trans
      (settlement_burn_lower_bound c.cfg _ _ _ _ _ hnew))

/-- The returned gross burn is the settlement burn for ordinary failures. -/
theorem finalizeReceipt_failure_tokensBurnt (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hpred : c.receipt.predecessorId ≠ systemAccount) :
    (finalizeReceipt c st raw (some err)).tokensBurnt =
      (Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
        (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false).tokensBurnt := by
  have ht := congrArg (fun t => t.2.2.2.2.2.1) (finalizeReceipt_failure_trace c st raw err)
  simpa [Exec.finalizationTrace, Receipt.isRefund, hpred] using ht

/-- Net token conservation over the actual returned execution: liquid/locked
balances, outgoing receipt backing, and burn after deducting the receiver reward.
Gas and configuration bounds are explicit; no conservation premise is assumed. -/
theorem finalizeReceipt_failure_net_conservation (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hwf : st.AccountsUnique)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hgas : raw.gasBurnt ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hfc : raw.gasBurntForFunctionCall ≤ raw.gasBurnt) :
    let final := finalizeReceipt c st raw (some err)
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt := by
  have hc := finalizeReceipt_failure_conservation c st raw err hwf hpred hsigner hreceipt hnew hgas
  have hr := finalizeReceipt_failure_reward_le_burn c st raw err hnew hratio hfc
  have hb := finalizeReceipt_failure_tokensBurnt c st raw err hpred
  dsimp only at hc hr ⊢
  rw [hb]
  omega

/-- Failed-receipt net conservation connected to action execution. -/
theorem applyActionReceipt_failure_net_conservation (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hrun : runReceiptActions c st = (raw, some err))
    (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hsigner : c.action.signerId ≠ systemAccount) (hreceipt : c.receipt.receipt = .action c.action)
    (hnew : c.cfg.accountCostIncrease = true)
    (hgas : raw.gasBurnt ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hfc : raw.gasBurntForFunctionCall ≤ raw.gasBurnt) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt := by
  simpa only [applyActionReceipt, Exec.commitStorage, hrun, Exec.totalFunds_storageAccounting] using
    finalizeReceipt_failure_net_conservation c st raw err hwf hpred hsigner hreceipt hnew hgas hratio hfc

/-- All state components other than account records and the receipt-id counter. -/
def ChainState.receiptFrame (st : ChainState) :=
  (st.accessKeys, st.storage, st.postponed, st.pendingDataCount, st.postponedByData, st.receivedData, st.delayed)

@[simp] theorem addBalanceRefund_frame (exec : Exec) (receiver : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).state.receiptFrame = exec.state.receiptFrame := rfl

@[simp] theorem addGasRefund_frame (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).state.receiptFrame = exec.state.receiptFrame := rfl

@[simp] theorem addFailureData_frame (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).state.receiptFrame = exec.state.receiptFrame := by
  unfold Exec.addFailureData
  dsimp only
  rw [failureDataFold_state]
  rfl

@[simp] theorem deliverResult_frame (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.deliverResult receiver outputs).state.receiptFrame = exec.state.receiptFrame := by
  unfold Exec.deliverResult
  split
  · simp only [Exec.addSuccessData, successDataFold_state]
    rfl
  · simp only [Exec.addFailureData, failureDataFold_state]
    rfl
  · rfl

@[simp] theorem finishReceiptResult_frame (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) :
    (exec.finishReceiptResult c failed).state.receiptFrame = exec.state.receiptFrame := by
  unfold Exec.finishReceiptResult
  rw [deliverResult_frame]
  split <;> rfl

@[simp] theorem creditReceiptReward_frame (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.receiptFrame = exec.state.receiptFrame := by
  unfold Exec.creditReceiptReward
  split <;> rfl

@[simp] theorem ite_frame (p : Prop) [Decidable p] (yes no : Exec) :
    (if p then yes else no).state.receiptFrame =
      if p then yes.state.receiptFrame else no.state.receiptFrame := by split <;> rfl

/-- Finalization cannot leak tentative storage, access-key or scheduler changes
from a failed action body. It may credit the receiver and allocate receipt ids. -/
theorem finalizeReceipt_failure_frame (c : ReceiptCtx) (st : ChainState) (raw : Exec) (err : RuntimeError) :
    (finalizeReceipt c st raw (some err)).state.receiptFrame = st.receiptFrame := by
  unfold finalizeReceipt
  simp only [finishReceiptResult_frame, creditReceiptReward_frame, ite_frame,
    addGasRefund_frame, addBalanceRefund_frame, ite_self]
  rfl

@[simp] theorem addBalanceRefund_account (exec : Exec) (receiver id : AccountId) (amount : Nat) :
    (exec.addBalanceRefund receiver amount).state.account? id = exec.state.account? id := rfl

@[simp] theorem addGasRefund_account (exec : Exec) (receiver id : AccountId) (pk : PublicKey) (amount : Nat) :
    (exec.addGasRefund receiver pk amount).state.account? id = exec.state.account? id := rfl

@[simp] theorem addFailureData_account (exec : Exec) (receiver id : AccountId) (outputs : List DataReceiver) :
    (exec.addFailureData receiver outputs).state.account? id = exec.state.account? id := by
  unfold Exec.addFailureData
  dsimp only
  rw [failureDataFold_state]
  rfl

@[simp] theorem creditReceiptReward_account_ne (exec : Exec) (cfg : RuntimeConfig) (receiver id : AccountId)
    (burnPrice purchasePrice : Nat) (hne : receiver ≠ id) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.account? id = exec.state.account? id := by
  unfold Exec.creditReceiptReward
  split
  · exact ChainState.account?_setAccount_ne _ _ _ _ hne
  · rfl

@[simp] theorem ite_account (p : Prop) [Decidable p] (yes no : Exec) (id : AccountId) :
    (if p then yes else no).state.account? id =
      if p then yes.state.account? id else no.state.account? id := by split <;> rfl

/-- Unrelated accounts retain their complete records across failed finalization. -/
theorem finalizeReceipt_failure_account_ne (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (id : AccountId) (hne : c.receipt.receiverId ≠ id) :
    (finalizeReceipt c st raw (some err)).state.account? id = st.account? id := by
  unfold finalizeReceipt
  simp only [finishReceiptResult_account, creditReceiptReward_account_ne _ _ _ _ _ _ hne,
    ite_account, addGasRefund_account, addBalanceRefund_account, ite_self]
  rfl

/-- Failed ordinary receipt conservation with gas premises derived from the
actual action attempt. Only state/configuration/receipt-shape premises remain. -/
theorem applyActionReceipt_failed_net_conservation (c : ReceiptCtx) (st : ChainState)
    (err : RuntimeError) (hfailed : (runReceiptActions c st).2 = some err)
    (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hsigner : c.action.signerId ≠ systemAccount) (hreceipt : c.receipt.receipt = .action c.action)
    (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt := by
  have hrun : runReceiptActions c st = ((runReceiptActions c st).1, some err) :=
    Prod.ext rfl hfailed
  have hg := runReceiptActions_gas_bounds c st
  exact applyActionReceipt_failure_net_conservation c st _ err hrun hwf hpred hsigner hreceipt hnew
    (hg.2.1.trans hg.2.2) hratio hg.1

end Near
