import NearRuntime.ReceiptInvariants
import NearRuntime.RefundInvariants

namespace Near
open Wasm.Near

theorem refund_runReceiptAction_gasBound (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action)
    (hrefund : c.receipt.isRefund = true) :
    (runReceiptAction c onlyAction isLast action).GasBound action.attachedGas := by
  unfold runReceiptAction
  simp only [chargeReceiptFee, hrefund, ite_true, pure_bind]
  exact gasBound_bind_left_zero (gasBound_checkReceiptAction c onlyAction action)
    (fun _ => applyAction_gasBound c isLast action)

theorem refund_runReceiptActionList_gasBound (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action)
    (hrefund : c.receipt.isRefund = true) :
    (runReceiptActionList c onlyAction actions).GasBound (Fees.totalPrepaid actions) := by
  induction actions with
  | nil => exact gasBound_pure _
  | cons action rest ih =>
    have h := (refund_runReceiptAction_gasBound c onlyAction rest.isEmpty action hrefund).bind (fun _ => ih)
    simpa [runReceiptActionList, Fees.totalPrepaid] using h

/-- System receipts pay no protocol execution fees. With no prepaid function
calls, the complete attempt spends zero gas, including failure paths. -/
theorem refund_receiptActionBody_gasBound_zero (c : ReceiptCtx)
    (hrefund : c.receipt.isRefund = true) (hprepaid : Fees.totalPrepaid c.action.actions = 0) :
    (receiptActionBody c).GasBound 0 := by
  unfold receiptActionBody
  simp only [chargeReceiptFee, hrefund, ite_true, pure_bind]
  have h := (refund_runReceiptActionList_gasBound c (c.action.actions.length == 1) c.action.actions hrefund).bind
    (fun _ => gasBound_checkStorageStake c.cfg c.receipt.receiverId)
  simpa only [hprepaid, Nat.add_zero] using h

theorem refund_runReceiptActions_gas_zero (c : ReceiptCtx) (st : ChainState)
    (hrefund : c.receipt.isRefund = true) (hprepaid : Fees.totalPrepaid c.action.actions = 0) :
    let raw := (runReceiptActions c st).1
    raw.gasBurntForFunctionCall = 0 ∧ raw.gasBurnt = 0 ∧ raw.gasUsed = 0 := by
  have h := refund_receiptActionBody_gasBound_zero c hrefund hprepaid
    { state := st, actorId := c.receipt.predecessorId }
  unfold runReceiptActions
  dsimp only
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId } with
  | mk result raw =>
    rw [he] at h
    have hf := h.functionCall_le_burnt
    have hb := h.burnt_le_used
    have hu := h.budget_bound
    dsimp only at hf hb hu
    have hz : raw.gasBurntForFunctionCall = 0 ∧ raw.gasBurnt = 0 ∧ raw.gasUsed = 0 := by omega
    cases result with
    | error error => exact hz
    | ok value => cases value; exact hz

/-- With no function-call gas there is no receiver gas reward. -/
theorem creditReceiptReward_zero (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (hfc : exec.gasBurntForFunctionCall = 0) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).reward = 0 := by
  unfold Exec.creditReceiptReward
  dsimp only
  split <;> simp [Exec.receiptRewardAmount, hfc]

/-- Failed system receipts do not recursively refund their deposits. Those
funds are reported as non-gas burn; only failure-data receipts may be emitted. -/
theorem finalizeReceipt_refund_failure_funds (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (err : RuntimeError) (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId = systemAccount)
    (hfc : raw.gasBurntForFunctionCall = 0) :
    let final := finalizeReceipt c st raw (some err)
    final.totalFunds c.cfg = st.totalBalance ∧ final.reward = 0 := by
  have hrefund : c.receipt.isRefund = true := by simp [Receipt.isRefund, hpred]
  let base := { rollbackReceipt st raw (some err) with
    tokensBurnt := 0, otherTokensBurnt := Fees.totalDeposit c.action.actions }
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasBurnt raw.gasBurnt false
  let rewarded := base.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let data := rewarded.addFailureData c.receipt.receiverId c.action.outputDataReceivers
  have hf : finalizeReceipt c st raw (some err) =
      { data with result := some (data.result.getD (.successValue [])) } := by
    simp [finalizeReceipt, hrefund, hpred, rollbackReceipt, Exec.finishReceiptResult, Exec.deliverResult, base, settlement, data, rewarded]
  have hz : rewarded.reward = 0 := creditReceiptReward_zero base c.cfg _ _ _ hfc
  have hb := creditReceiptReward_totalFunds c.cfg base c.receipt.receiverId
    settlement.burnPrice c.action.gasPrice hwf
  change rewarded.totalFunds c.cfg = base.totalFunds c.cfg + rewarded.reward at hb
  rw [hz] at hb
  have hbase : base.totalFunds c.cfg = st.totalBalance := by
    simp [base, rollbackReceipt, Exec.totalFunds, receiptsFunds]
  rw [hbase, Nat.add_zero] at hb
  dsimp only
  rw [hf]
  change data.totalFunds c.cfg = st.totalBalance ∧ rewarded.reward = 0
  exact ⟨by simpa only [data, addFailureData_totalFunds] using hb, hz⟩

/-- Failed refund backing is burnt exactly once, with no gas charge or reward. -/
theorem applyActionReceipt_refund_failed_conservation (c : ReceiptCtx) (st : ChainState)
    (err : RuntimeError) (hfailed : (runReceiptActions c st).2 = some err)
    (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId = systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action)
    (hprepaid : Fees.totalPrepaid c.action.actions = 0) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt + final.otherTokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt := by
  let raw := (runReceiptActions c st).1
  have hrun : runReceiptActions c st = (raw, some err) := Prod.ext rfl hfailed
  have hrefund : c.receipt.isRefund = true := by simp [Receipt.isRefund, hpred]
  have hz := refund_runReceiptActions_gas_zero c st hrefund hprepaid
  have hf := finalizeReceipt_refund_failure_funds c st raw err hwf hpred hz.1
  have ht := congrArg (fun trace => trace.2.2.2.2.2) (finalizeReceipt_failure_trace c st raw err)
  have hburn : ((finalizeReceipt c st raw (some err)).tokensBurnt,
      (finalizeReceipt c st raw (some err)).otherTokensBurnt) = (0, Fees.totalDeposit c.action.actions) := by
    simpa [Exec.finalizationTrace, hrefund] using ht
  have hi : Fees.receiptFunds c.cfg c.receipt = Fees.totalDeposit c.action.actions := by
    simp [Fees.receiptFunds, hreceipt, hrefund]
  simp only [applyActionReceipt, hrun]
  dsimp only at hf ⊢
  have hb := congrArg Prod.fst hburn
  have ho := congrArg Prod.snd hburn
  dsimp only at hb ho
  rw [hf.1, hf.2, hb, ho, hi]
  simp

/-- Successful zero-gas system finalization adds no refunds, burn or reward. -/
theorem finalizeReceipt_refund_success_funds (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (hwf : raw.state.AccountsUnique) (hrefund : c.receipt.isRefund = true)
    (hfc : raw.gasBurntForFunctionCall = 0) :
    let final := finalizeReceipt c st raw none
    final.totalFunds c.cfg = raw.totalFunds c.cfg ∧ final.tokensBurnt = 0 ∧
      final.otherTokensBurnt = 0 ∧ final.reward = 0 := by
  let base := { raw with tokensBurnt := 0, otherTokensBurnt := 0 }
  let created := (st.account? c.receipt.receiverId).isNone && (raw.state.account? c.receipt.receiverId).isSome
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasUsed raw.gasBurnt created
  let rewarded := base.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let finished := rewarded.finishReceiptResult c none
  have hf : finalizeReceipt c st raw none =
      { finished with result := some (finished.result.getD (.successValue [])) } := by
    simp [finalizeReceipt, hrefund, rollbackReceipt, base, created, settlement, rewarded, finished]
  have hz : rewarded.reward = 0 := creditReceiptReward_zero base c.cfg _ _ _ hfc
  have hb := creditReceiptReward_totalFunds c.cfg base c.receipt.receiverId
    settlement.burnPrice c.action.gasPrice hwf
  change rewarded.totalFunds c.cfg = raw.totalFunds c.cfg + rewarded.reward at hb
  rw [hz, Nat.add_zero] at hb
  have ht := congrArg (fun trace => trace.2.2.2.2.2)
    (creditReceiptReward_trace base c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice)
  have hp : (rewarded.tokensBurnt, rewarded.otherTokensBurnt) = (0, 0) := by
    simpa [Exec.finalizationTrace, base] using ht
  dsimp only
  rw [hf]
  have ht' := finishReceiptResult_trace rewarded c none
  have hburn := congrArg (fun t => t.2.2.2.2.2) ht'
  change (finished.tokensBurnt, finished.otherTokensBurnt) = (rewarded.tokensBurnt, rewarded.otherTokensBurnt) at hburn
  change finished.totalFunds c.cfg = raw.totalFunds c.cfg ∧ finished.tokensBurnt = 0 ∧
    finished.otherTokensBurnt = 0 ∧ finished.reward = 0
  rw [finishReceiptResult_totalFunds, finishReceiptResult_reward]
  exact ⟨hb, congrArg Prod.fst (hburn.trans hp), congrArg Prod.snd (hburn.trans hp), hz⟩

@[simp] theorem refundAllowance_account (st : ChainState) (receiver id : AccountId) (pk : PublicKey) (amount : Nat) :
    (st.refundAllowance receiver pk amount).account? id = st.account? id := by
  unfold ChainState.refundAllowance
  split
  · rfl
  · split <;> rfl

theorem refundAllowance_accountsUnique (st : ChainState) (id : AccountId) (pk : PublicKey) (amount : Nat)
    (hwf : st.AccountsUnique) : (st.refundAllowance id pk amount).AccountsUnique := by
  have ha := congrArg ChainState.accounts (ChainState.refundAllowance_frame st id pk amount)
  change (st.refundAllowance id pk amount).accounts = st.accounts at ha
  simpa only [ChainState.AccountsUnique, ha] using hwf

/-- The successful transfer state, including best-effort current-key restoration. -/
def refundTransferState (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat) : ChainState :=
  let credited := st.setAccount c.receipt.receiverId { account with amount := account.amount + amount }
  if c.receipt.isGasRefund then credited.refundAllowance c.receipt.receiverId c.action.signerPublicKey amount else credited

theorem refundTransferState_accountsUnique (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat)
    (hwf : st.AccountsUnique) : (refundTransferState c st account amount).AccountsUnique := by
  unfold refundTransferState
  dsimp only
  split
  · exact refundAllowance_accountsUnique _ _ _ _ (hwf.setAccount _ _)
  · exact hwf.setAccount _ _

theorem refundTransferState_totalBalance (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat)
    (hwf : st.AccountsUnique) (ha : st.account? c.receipt.receiverId = some account) :
    (refundTransferState c st account amount).totalBalance = st.totalBalance + amount := by
  have hb := ChainState.totalBalance_setAccount st c.receipt.receiverId
    { account with amount := account.amount + amount } account hwf ha
  dsimp only at hb
  unfold refundTransferState
  dsimp only
  split
  · rw [ChainState.refundAllowance_totalBalance]
    omega
  · omega

/-- Exact single-refund evaluation before finalization, for an existing receiver. -/
theorem refund_receiptActionBody_run (c : ReceiptCtx) (before : Exec) (account : Account) (amount : Nat)
    (hrefund : c.receipt.isRefund = true) (hactions : c.action.actions = [.transfer amount])
    (ha : before.state.account? c.receipt.receiverId = some account) :
    (receiptActionBody c).run.run before =
      let after := { before with state := refundTransferState c before.state account amount }
      let deficit := storageStakeDeficit c.cfg { account with amount := account.amount + amount }
      if deficit > 0 then (.error (.lackBalanceForState c.receipt.receiverId deficit), after) else (.ok (), after) := by
  by_cases hd : storageStakeDeficit c.cfg { account with amount := account.amount + amount } > 0
  all_goals cases hg : c.receipt.isGasRefund <;>
    simp [hd, -ExceptT.run_bind, -StateT.run_bind, receiptActionBody, hactions, runReceiptActionList,
      runReceiptAction, chargeReceiptFee, hrefund, checkReceiptAction, checkActionAccount,
      checkActorPermissions, applyAction, getState, putAccount, modifyState, checkStorageStake,
      refundTransferState, ha, hg, ChainState.account?_setAccount_self]

/-- A missing receiver fails before executing a system transfer, even for an
implicit-account name: refunds cannot create implicit accounts. -/
theorem refund_receiptActionBody_missing (c : ReceiptCtx) (before : Exec) (amount : Nat)
    (hrefund : c.receipt.isRefund = true) (hactions : c.action.actions = [.transfer amount])
    (ha : before.state.account? c.receipt.receiverId = none) :
    (receiptActionBody c).run.run before = (.error (.accountDoesNotExist c.receipt.receiverId), before) := by
  simp [-ExceptT.run_bind, -StateT.run_bind, receiptActionBody, hactions, runReceiptActionList,
    runReceiptAction, chargeReceiptFee, hrefund, checkReceiptAction, checkActionAccount, getState, ha]

/-- Successful system transfers require an existing receiver and have exactly
the credited transfer state; storage-staking failure is handled by rollback. -/
theorem refund_success_raw (c : ReceiptCtx) (st : ChainState) (amount : Nat)
    (hrefund : c.receipt.isRefund = true) (hactions : c.action.actions = [.transfer amount])
    (hsuccess : (runReceiptActions c st).2 = none) :
    ∃ account, st.account? c.receipt.receiverId = some account ∧
      (runReceiptActions c st).1 =
        { state := refundTransferState c st account amount, actorId := c.receipt.predecessorId } := by
  cases ha : st.account? c.receipt.receiverId with
  | none =>
    have hb := refund_receiptActionBody_missing c
      { state := st, actorId := c.receipt.predecessorId } amount hrefund hactions ha
    unfold runReceiptActions at hsuccess
    dsimp only at hsuccess
    rw [hb] at hsuccess
    contradiction
  | some account =>
    have hb := refund_receiptActionBody_run c
      { state := st, actorId := c.receipt.predecessorId } account amount hrefund hactions ha
    refine ⟨account, rfl, ?_⟩
    unfold runReceiptActions
    dsimp only
    rw [hb]
    dsimp only
    split_ifs <;> rfl

/-- Successful system refunds credit their backing exactly once, including
current-key allowance restoration, without gas burn or new backed receipts. -/
theorem applyActionReceipt_refund_success_conservation (c : ReceiptCtx) (st : ChainState) (amount : Nat)
    (hsuccess : (runReceiptActions c st).2 = none) (hwf : st.AccountsUnique)
    (hpred : c.receipt.predecessorId = systemAccount) (hreceipt : c.receipt.receipt = .action c.action)
    (hactions : c.action.actions = [.transfer amount]) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt + final.otherTokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt := by
  have hrefund : c.receipt.isRefund = true := by simp [Receipt.isRefund, hpred]
  obtain ⟨account, ha, hraw⟩ := refund_success_raw c st amount hrefund hactions hsuccess
  let raw := (runReceiptActions c st).1
  have hrun : runReceiptActions c st = (raw, none) := Prod.ext rfl hsuccess
  have hu : raw.state.AccountsUnique := by
    change (runReceiptActions c st).1.state.AccountsUnique
    rw [hraw]
    exact refundTransferState_accountsUnique c st account amount hwf
  have hfc : raw.gasBurntForFunctionCall = 0 := by
    change (runReceiptActions c st).1.gasBurntForFunctionCall = 0
    rw [hraw]
  have hf := finalizeReceipt_refund_success_funds c st raw hu hrefund hfc
  have hb : raw.totalFunds c.cfg = st.totalBalance + amount := by
    change (runReceiptActions c st).1.totalFunds c.cfg = _
    rw [hraw]
    simpa [Exec.totalFunds, receiptsFunds] using refundTransferState_totalBalance c st account amount hwf ha
  have hi : Fees.receiptFunds c.cfg c.receipt = amount := by
    simp [Fees.receiptFunds, hreceipt, hrefund, Fees.totalDeposit, hactions, Action.deposit]
  simp only [applyActionReceipt, hrun]
  dsimp only at hf ⊢
  rw [hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hb, hi]
  simp

/-- Constructor-shaped balance and gas refunds conserve account/in-flight funds
plus all reported burn, on both success and failure. -/
theorem applyActionReceipt_refund_conservation (c : ReceiptCtx) (st : ChainState) (amount : Nat)
    (hwf : st.AccountsUnique) (hpred : c.receipt.predecessorId = systemAccount)
    (hreceipt : c.receipt.receipt = .action c.action) (hactions : c.action.actions = [.transfer amount]) :
    let final := applyActionReceipt c st
    final.totalFunds c.cfg + (final.tokensBurnt + final.otherTokensBurnt - final.reward) =
      st.totalBalance + Fees.receiptFunds c.cfg c.receipt := by
  cases hfailed : (runReceiptActions c st).2 with
  | none => exact applyActionReceipt_refund_success_conservation c st amount hfailed hwf hpred hreceipt hactions
  | some err =>
    exact applyActionReceipt_refund_failed_conservation c st err hfailed hwf hpred hreceipt
      (by simp [Fees.totalPrepaid, hactions, Action.attachedGas])

end Near
