import NearRuntime.ActionFunding
import NearRuntime.RefundReceiptInvariants

namespace Near
open Wasm.Near

/-- The exact successful-receipt settlement, including the native account-
creation flag rather than assuming that it is false. -/
def successSettlement (c : ReceiptCtx) (st : ChainState) (raw : Exec) : Fees.GasSettlement :=
  Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasUsed raw.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (raw.state.account? c.receipt.receiverId).isSome)

/-- Successful finalization keeps execution observations and explicit subsidy;
ordinary gas burn is precisely the settlement's gross burn. -/
theorem finalizeReceipt_success_trace (c : ReceiptCtx) (st : ChainState) (raw : Exec) :
    (finalizeReceipt c st raw none).finalizationTrace =
      (raw.gasBurnt, raw.gasUsed, raw.gasBurntForFunctionCall, raw.logs, raw.subsidizedAmount,
        if c.receipt.isRefund then 0 else (successSettlement c st raw).tokensBurnt, 0) := by
  unfold finalizeReceipt
  simp only [setResult_trace, addFailureData_trace, addCompletionData_trace, creditReceiptReward_trace,
    ite_trace, addBalanceRefund_trace, addGasRefund_trace, ite_self]
  simp [rollbackReceipt, Exec.finalizationTrace, successSettlement]

/-- Ordinary successful finalization adds only the unused-gas refund and the
receiver reward to the already-funded raw action ledger. -/
theorem finalizeReceipt_success_funds (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (hwf : raw.state.AccountsUnique) (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hsigner : c.action.signerId ≠ systemAccount) :
    (finalizeReceipt c st raw none).totalFunds c.cfg =
      raw.totalFunds c.cfg + (successSettlement c st raw).refund + (finalizeReceipt c st raw none).reward := by
  let settlement := successSettlement c st raw
  let base := { raw with tokensBurnt := settlement.tokensBurnt, otherTokensBurnt := 0 }
  let gas := if settlement.refund > 0 then
    base.addGasRefund c.action.signerId c.action.signerPublicKey settlement.refund else base
  have hg : gas.totalFunds c.cfg = raw.totalFunds c.cfg + settlement.refund := by
    dsimp only [gas]
    split
    · rw [addGasRefund_totalFunds]; rfl
    · rename_i h
      have hz : settlement.refund = 0 := by omega
      simp [hz, base, Exec.totalFunds]
  have hgu : gas.state.AccountsUnique := by
    dsimp only [gas]
    split <;> simpa [base] using hwf
  have hr := creditReceiptReward_totalFunds c.cfg gas c.receipt.receiverId
    settlement.burnPrice c.action.gasPrice hgu
  rw [hg] at hr
  have hrefund : c.receipt.isRefund = false := by simp [Receipt.isRefund, hpred]
  let rewarded := gas.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let data := rewarded.addCompletionData c.receipt.receiverId c.action.outputDataReceivers
  have hf : finalizeReceipt c st raw none =
      { data with result := some (data.result.getD (.successValue [])) } := by
    simp [finalizeReceipt, rollbackReceipt, hrefund, hsigner, base, gas, settlement, rewarded, data, successSettlement]
  rw [hf]
  change data.totalFunds c.cfg = raw.totalFunds c.cfg + settlement.refund + data.reward
  simpa only [data, addCompletionData_totalFunds, addCompletionData_reward] using hr

/-- Funded ordinary receipts conserve the complete incoming
ledger, outgoing receipt backing, explicit subsidy, gross gas burn and receiver
reward. The action-body funding rule is a compositional premise; concrete public
theorems below discharge it from executable action implementations. -/
theorem applyActionReceipt_success_conservation_of_funded (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hbody : (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions))
    (hsuccess : (runReceiptActions c st).2 = none) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + final.tokensBurnt =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount + final.reward := by
  let raw := (runReceiptActions c st).1
  let final := finalizeReceipt c st raw none
  have hf := runReceiptActions_success_funded_of_body c st hwf hbody hsuccess
  change raw.state.AccountsUnique ∧ raw.totalFunds c.cfg + raw.gasBurnt * c.action.gasPrice =
    st.totalBalance + Fees.totalDeposit c.action.actions + raw.subsidizedAmount + raw.gasUsed * c.action.gasPrice at hf
  have hg := runReceiptActions_gas_bounds c st
  change raw.gasBurntForFunctionCall ≤ raw.gasBurnt ∧ raw.gasBurnt ≤ raw.gasUsed ∧
    raw.gasUsed ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions at hg
  have hs := Fees.settleGas_conservation c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasUsed raw.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (raw.state.account? c.receipt.receiverId).isSome) hnew hg.2.2 hg.2.1
  change (successSettlement c st raw).refund + (successSettlement c st raw).tokensBurnt +
    (raw.gasUsed - raw.gasBurnt) * c.action.gasPrice = _ at hs
  have hfunds := finalizeReceipt_success_funds c st raw hf.1 hpred hsigner
  have ht := finalizeReceipt_success_trace c st raw
  have hburn := congrArg (fun trace => trace.2.2.2.2.2.1) ht
  have hsubsidy := congrArg (fun trace => trace.2.2.2.2.1) ht
  simp only [Exec.finalizationTrace, Receipt.isRefund, beq_eq_false_iff_ne.mpr hpred,
    Bool.false_eq_true, ite_false] at hburn hsubsidy
  have hpartition : raw.gasBurnt * c.action.gasPrice +
      (raw.gasUsed - raw.gasBurnt) * c.action.gasPrice = raw.gasUsed * c.action.gasPrice := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hg.2.1]
  have hi : Fees.receiptFunds c.cfg c.receipt = Fees.totalDeposit c.action.actions +
      Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions * c.action.gasPrice := by
    simp [Fees.receiptFunds, hreceipt, Receipt.isRefund, hpred]
  have hfinal : applyActionReceipt c st = final := by simp [applyActionReceipt, final, raw, hsuccess]
  dsimp only
  rw [hfinal, hi]
  change final.totalFunds c.cfg + final.tokensBurnt = _
  change final.totalFunds c.cfg = raw.totalFunds c.cfg + (successSettlement c st raw).refund + final.reward at hfunds
  change final.tokensBurnt = _ at hburn
  change final.subsidizedAmount = _ at hsubsidy
  omega

/-- Successful finalization credits at most the recorded function-call reward. -/
theorem finalizeReceipt_success_reward_le (c : ReceiptCtx) (st : ChainState) (raw : Exec) :
    (finalizeReceipt c st raw none).reward ≤
      raw.receiptRewardAmount c.cfg (successSettlement c st raw).burnPrice c.action.gasPrice := by
  unfold finalizeReceipt
  dsimp only
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false, addCompletionData_reward]
  apply (creditReceiptReward_reward_le _ _ _ _ _).trans
  simp only [ite_rewardAmount, addGasRefund_rewardAmount, addBalanceRefund_rewardAmount, ite_self]
  rfl

/-- An already-existing receiver cannot trigger the account-creation surcharge. -/
theorem successSettlement_existing (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (hexists : (st.account? c.receipt.receiverId).isSome = true) :
    successSettlement c st raw = Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
      (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasUsed raw.gasBurnt false := by
  cases he : st.account? c.receipt.receiverId with
  | none => simp [he] at hexists
  | some account => simp [successSettlement, he]

/-- Account-creation charges add to gross burn, so they cannot reduce the
backing available for receiver rewards. This also covers newly created accounts. -/
theorem settlement_burn_lower_bound_created (cfg : RuntimeConfig) (purchase current prepaid used burnt : Nat)
    (created : Bool) (hnew : cfg.accountCostIncrease = true) :
    burnt * (Fees.settleGas cfg purchase current prepaid used burnt created).burnPrice ≤
      (Fees.settleGas cfg purchase current prepaid used burnt created).tokensBurnt := by
  have hd : min purchase current - purchase = 0 := Nat.sub_eq_zero_of_le (Nat.min_le_left _ _)
  simp [Fees.settleGas, hnew, hd]
  omega

/-- Receiver rewards are backed by gross burn under the configured reward
fraction, for ordinary receipt execution, including account creation. -/
theorem applyActionReceipt_success_net_conservation_of_funded (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hbody : (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions))
    (hsuccess : (runReceiptActions c st).2 = none) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount := by
  let raw := (runReceiptActions c st).1
  have hf := applyActionReceipt_success_conservation_of_funded c st hwf hpred hsigner hreceipt hnew hbody hsuccess
  have hfinal : applyActionReceipt c st = finalizeReceipt c st raw none := by simp [applyActionReceipt, raw, hsuccess]
  have ht := congrArg (fun trace => trace.2.2.2.2.2.1) (finalizeReceipt_success_trace c st raw)
  have hr := finalizeReceipt_success_reward_le c st raw
  have hg := runReceiptActions_gas_bounds c st
  have hbound := receiptRewardAmount_le raw c.cfg (successSettlement c st raw).burnPrice c.action.gasPrice hnew hratio hg.1
  have hlower := settlement_burn_lower_bound_created c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasUsed raw.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (raw.state.account? c.receipt.receiverId).isSome) hnew
  change raw.gasBurnt * (successSettlement c st raw).burnPrice ≤ (successSettlement c st raw).tokensBurnt at hlower
  simp only [Exec.finalizationTrace, Receipt.isRefund, beq_eq_false_iff_ne.mpr hpred,
    Bool.false_eq_true, ite_false] at ht
  have hreward : (applyActionReceipt c st).reward ≤ (applyActionReceipt c st).tokensBurnt := by
    rw [hfinal]
    exact (hr.trans hbound).trans (by simpa only [ht] using hlower)
  dsimp only at hf ⊢
  omega

/-- A funded ordinary receipt conserves net funds on success
and failure. Concrete action-family theorems discharge the funding premise.
Explicit subsidy survives success and is rolled back on receipt failure. -/
theorem applyActionReceipt_net_conservation_of_funded (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hbody : (receiptActionBody c).Funded c.cfg c.action.gasPrice (Fees.totalDeposit c.action.actions)) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount := by
  cases he : (runReceiptActions c st).2 with
  | none =>
    exact applyActionReceipt_success_net_conservation_of_funded c st hwf hpred hsigner
      hreceipt hnew hratio hbody he
  | some error =>
    have hf := applyActionReceipt_failed_net_conservation c st error he hwf hpred hsigner hreceipt hnew hratio
    have ht := congrArg (fun trace => trace.2.2.2.2.1)
      (finalizeReceipt_failure_trace c st (runReceiptActions c st).1 error)
    have hsubsidy : (applyActionReceipt c st).subsidizedAmount = 0 := by
      simpa only [applyActionReceipt, he, Exec.finalizationTrace] using ht
    dsimp only at hf ⊢
    rw [hsubsidy, Nat.add_zero]
    exact hf

/-- The concrete function-call implementation discharges the entire action-body funding rule. -/
theorem applyActionReceipt_functionCalls_success_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hactions : ∀ action ∈ c.action.actions, FunctionCallFundingAction action)
    (hsuccess : (runReceiptActions c st).2 = none) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + final.tokensBurnt =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount + final.reward :=
  applyActionReceipt_success_conservation_of_funded c st hwf hpred hsigner hreceipt hnew
    (funded_receiptActionBody c hreceiver hactions) hsuccess

/-- The concrete function-call implementation discharges the entire action-body funding rule. -/
theorem applyActionReceipt_functionCalls_success_net_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hactions : ∀ action ∈ c.action.actions, FunctionCallFundingAction action)
    (hsuccess : (runReceiptActions c st).2 = none) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount :=
  applyActionReceipt_success_net_conservation_of_funded c st hwf hpred hsigner hreceipt hnew hratio
    (funded_receiptActionBody c hreceiver hactions) hsuccess

/-- The concrete function-call implementation discharges the entire action-body funding rule. -/
theorem applyActionReceipt_functionCalls_net_conservation (c : ReceiptCtx) (st : ChainState)
    (hwf : st.AccountsUnique) (hreceiver : c.receipt.receiverId ≠ systemAccount)
    (hpred : c.receipt.predecessorId ≠ systemAccount) (hsigner : c.action.signerId ≠ systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hactions : ∀ action ∈ c.action.actions, FunctionCallFundingAction action) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt + final.subsidizedAmount :=
  applyActionReceipt_net_conservation_of_funded c st hwf hpred hsigner hreceipt hnew hratio
    (funded_receiptActionBody c hreceiver hactions)

end Near
