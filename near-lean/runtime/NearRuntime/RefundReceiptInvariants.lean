import NearRuntime.ReceiptInvariants
import NearRuntime.RefundInvariants

namespace Near
open Wasm.Near

/-- Only attached call gas can increase function-call burn; protocol fees cannot. -/
def ExecM.FunctionCallBound (operation : ExecM α) (budget : Nat) : Prop :=
  ∀ before, (operation.run.run before).2.gasBurntForFunctionCall ≤ before.gasBurntForFunctionCall + budget

theorem functionCallBound_of_gasBound {operation : ExecM α} {budget : Nat}
    (h : operation.GasBound budget) : operation.FunctionCallBound budget := by
  intro before
  have h := h before
  rcases h with ⟨_, _, _, hfc, hb, hu⟩
  omega

theorem functionCallBound_bind {operation : ExecM α} {next : α → ExecM β} {first second : Nat}
    (hfirst : operation.FunctionCallBound first) (hsecond : ∀ value, (next value).FunctionCallBound second) :
    (operation >>= next).FunctionCallBound (first + second) := by
  intro before
  rw [execM_run_bind]
  have h := hfirst before
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at h
    dsimp only at h
    cases result with
    | error error => dsimp only; omega
    | ok value => have hn := hsecond value middle; dsimp only; omega

theorem functionCallBound_zero_left {operation : ExecM α} {next : α → ExecM β} {budget : Nat}
    (hfirst : operation.FunctionCallBound 0) (hsecond : ∀ value, (next value).FunctionCallBound budget) :
    (operation >>= next).FunctionCallBound budget := by
  simpa only [Nat.zero_add] using functionCallBound_bind hfirst hsecond

theorem functionCallBound_fee (isRefund : Bool) (fee : Nat) :
    (chargeReceiptFee isRefund fee).FunctionCallBound 0 := by intro before; exact Nat.le_refl _

theorem runReceiptAction_functionCallBound (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).FunctionCallBound action.attachedGas := by
  unfold runReceiptAction
  apply functionCallBound_zero_left (functionCallBound_fee _ _)
  intro _
  apply functionCallBound_zero_left (functionCallBound_of_gasBound (gasBound_checkReceiptAction c onlyAction action))
  intro _
  exact functionCallBound_of_gasBound (applyAction_gasBound c isLast action)

theorem runReceiptActionAt_functionCallBound (c : ReceiptCtx) (onlyAction isLast : Bool)
    (action : Action) (index : Nat) :
    (runReceiptActionAt c onlyAction isLast action index).FunctionCallBound action.attachedGas := by
  cases action <;> try exact runReceiptAction_functionCallBound c onlyAction isLast _
  cases he : actionRandomSeed c index <;> simp only [runReceiptActionAt, he]
  · intro before; exact Nat.le_add_right _ _
  · exact runReceiptAction_functionCallBound _ onlyAction isLast _

theorem runReceiptActionList_functionCallBound (c : ReceiptCtx) (onlyAction : Bool)
    (actions : List Action) (index : Nat) :
    (runReceiptActionList c onlyAction actions index).FunctionCallBound (Fees.totalPrepaid actions) := by
  induction actions generalizing index with
  | nil => intro before; exact Nat.le_refl _
  | cons action rest ih =>
    have hm := functionCallBound_of_gasBound
      (gasBound_modify (fun e : Exec => { e with failureIndex := some index }) 0
        (fun _ => GasDelta.of_fields _ _ _ rfl rfl rfl))
    have h := functionCallBound_zero_left hm (fun _ =>
      functionCallBound_bind (runReceiptActionAt_functionCallBound c onlyAction rest.isEmpty action index)
        (fun _ => ih (index + 1)))
    simpa [runReceiptActionList, Fees.totalPrepaid] using h

theorem receiptActionBody_functionCallBound (c : ReceiptCtx) :
    (receiptActionBody c).FunctionCallBound (Fees.totalPrepaid c.action.actions) := by
  unfold receiptActionBody
  apply functionCallBound_zero_left (functionCallBound_fee _ _)
  intro _
  have hm := functionCallBound_of_gasBound
    (gasBound_modify (fun e : Exec => { e with failureIndex := none }) 0
      (fun _ => GasDelta.of_fields _ _ _ rfl rfl rfl))
  have h := functionCallBound_bind
    (runReceiptActionList_functionCallBound c (c.action.actions.length == 1) c.action.actions 0)
    (fun _ => functionCallBound_zero_left hm (fun _ =>
      functionCallBound_of_gasBound (gasBound_checkStorageStake c.cfg c.receipt.receiverId)))
  simpa only [Nat.add_zero] using h

/-- Zero prepaid gas implies zero function-call burn, while receipt gas remains observable. -/
theorem refund_runReceiptActions_functionCallGas_zero (c : ReceiptCtx) (st : ChainState)
    (hprepaid : Fees.totalPrepaid c.action.actions = 0) :
    (runReceiptActions c st).1.gasBurntForFunctionCall = 0 := by
  have h := receiptActionBody_functionCallBound c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting }
  unfold runReceiptActions
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw =>
    rw [he] at h
    dsimp only at h
    rw [hprepaid] at h
    dsimp only
    rw [he]
    cases result with
    | error error => dsimp only; omega
    | ok value => cases value; dsimp only; omega

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

/-- Failed refund backing is burnt exactly once, with no token fee or reward. -/
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
  have hz := refund_runReceiptActions_functionCallGas_zero c st hprepaid
  have hf := finalizeReceipt_refund_failure_funds c st raw err hwf hpred hz
  have ht := congrArg (fun trace => trace.2.2.2.2.2) (finalizeReceipt_failure_trace c st raw err)
  have hburn : ((finalizeReceipt c st raw (some err)).tokensBurnt,
      (finalizeReceipt c st raw (some err)).otherTokensBurnt) = (0, Fees.totalDeposit c.action.actions) := by
    simpa [Exec.finalizationTrace, hrefund] using ht
  have hi : Fees.receiptFunds c.cfg c.receipt = Fees.totalDeposit c.action.actions := by
    simp [Fees.receiptFunds, hreceipt, hrefund]
  simp only [applyActionReceipt, Exec.commitStorage, hrun, Exec.totalFunds_storageAccounting]
  dsimp only at hf ⊢
  have hb := congrArg Prod.fst hburn
  have ho := congrArg Prod.snd hburn
  dsimp only at hb ho
  rw [hf.1, hf.2, hb, ho, hi]
  simp

theorem completionDataFold_state (receiver : AccountId) (data : Option Bytes) (outputs : List DataReceiver)
    (st : ChainState) (receipts : List Receipt) :
    (outputs.foldl (completionDataStep receiver data) (st, receipts)).1 =
      { st with nextId := st.nextId + outputs.length } := by
  induction outputs generalizing st receipts with
  | nil => rfl
  | cons output rest ih =>
    simp only [List.foldl_cons, completionDataStep, ChainState.freshId]
    rw [ih]
    simp only [List.length_cons]
    congr 1; omega

theorem completionDataFold_funds (cfg : RuntimeConfig) (receiver : AccountId) (data : Option Bytes)
    (outputs : List DataReceiver) (st : ChainState) (receipts : List Receipt) :
    receiptsFunds cfg (outputs.foldl (completionDataStep receiver data) (st, receipts)).2 = receiptsFunds cfg receipts := by
  induction outputs generalizing st receipts with
  | nil => rfl
  | cons output rest ih =>
    simp only [List.foldl_cons, completionDataStep, ChainState.freshId]
    rw [ih]
    simp [receiptsFunds, Fees.receiptFunds]

@[simp] theorem addCompletionData_totalFunds (cfg : RuntimeConfig) (exec : Exec) (receiver : AccountId)
    (outputs : List DataReceiver) : (exec.addCompletionData receiver outputs).totalFunds cfg = exec.totalFunds cfg := by
  cases hr : exec.result with
  | none => simp [Exec.addCompletionData, hr, Exec.totalFunds, receiptsFunds_append,
      completionDataFold_state, completionDataFold_funds, ChainState.totalBalance]; rfl
  | some status => cases status <;> simp [Exec.addCompletionData, hr, Exec.totalFunds, receiptsFunds_append,
      completionDataFold_state, completionDataFold_funds, ChainState.totalBalance] <;> rfl

@[simp] theorem addCompletionData_trace (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addCompletionData receiver outputs).finalizationTrace = exec.finalizationTrace := by
  cases hr : exec.result with
  | none => simp [Exec.addCompletionData, hr, Exec.finalizationTrace]
  | some status => cases status <;> simp [Exec.addCompletionData, hr, Exec.finalizationTrace]

@[simp] theorem addCompletionData_reward (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) :
    (exec.addCompletionData receiver outputs).reward = exec.reward := by
  cases hr : exec.result with
  | none => simp [Exec.addCompletionData, hr]
  | some status => cases status <;> simp [Exec.addCompletionData, hr]

/-- Successful system finalization adds no monetary refunds, burn or reward; completion data has zero backing. -/
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
  have hp : (data.tokensBurnt, data.otherTokensBurnt) = (0, 0) := by
    have htrace := congrArg (fun trace => trace.2.2.2.2.2)
      (addCompletionData_trace rewarded c.receipt.receiverId c.action.outputDataReceivers)
    change (data.tokensBurnt, data.otherTokensBurnt) = (rewarded.tokensBurnt, rewarded.otherTokensBurnt) at htrace
    exact htrace.trans ht
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

/-- Refunds report execution gas even though settlement charges no token fees. -/
def refundExecutionGas (c : ReceiptCtx) (amount : Nat) : Nat :=
  c.cfg.fees.actionFees.newActionReceipt.execution + Fees.exec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId (.transfer amount)

/-- Exact single-refund evaluation before finalization, for an existing receiver. -/
theorem refund_receiptActionBody_run (c : ReceiptCtx) (before : Exec) (account : Account) (amount : Nat)
    (hrefund : c.receipt.isRefund = true) (hactions : c.action.actions = [.transfer amount])
    (ha : before.state.account? c.receipt.receiverId = some account) :
    (receiptActionBody c).run.run before =
      let after := { before with
        state := refundTransferState c before.state account amount
        gasBurnt := before.gasBurnt + refundExecutionGas c amount,
        gasUsed := before.gasUsed + refundExecutionGas c amount, failureIndex := none }
      let deficit := storageStakeDeficit c.cfg { account with amount := account.amount + amount }
      if deficit > 0 then (.error (.lackBalanceForState c.receipt.receiverId deficit), after) else (.ok (), after) := by
  by_cases hd : storageStakeDeficit c.cfg { account with amount := account.amount + amount } > 0
  all_goals cases hg : c.receipt.isGasRefund <;>
    simp [hd, -StateT.run_bind, receiptActionBody, hactions, runReceiptActionList, runReceiptActionAt,
      runReceiptAction, chargeReceiptFee, hrefund, checkReceiptAction, checkActionAccount,
      checkActorPermissions, applyAction, getState, putAccount, modifyState, checkStorageStake,
      refundTransferState, refundExecutionGas, burnGas, ha, hg, ChainState.account?_setAccount_self, Nat.add_assoc]

/-- A missing receiver fails before executing a system transfer, even for an
implicit-account name: refunds cannot create implicit accounts. -/
theorem refund_receiptActionBody_missing (c : ReceiptCtx) (before : Exec) (amount : Nat)
    (hrefund : c.receipt.isRefund = true) (hactions : c.action.actions = [.transfer amount])
    (ha : before.state.account? c.receipt.receiverId = none) :
    (receiptActionBody c).run.run before = (.error (.accountDoesNotExist c.receipt.receiverId),
      { before with
        gasBurnt := before.gasBurnt + refundExecutionGas c amount
        gasUsed := before.gasUsed + refundExecutionGas c amount, failureIndex := some 0 }) := by
  simp [-StateT.run_bind, receiptActionBody, hactions, runReceiptActionList, runReceiptActionAt,
    runReceiptAction, chargeReceiptFee, hrefund, checkReceiptAction, checkActionAccount, getState, burnGas, refundExecutionGas, ha, Nat.add_assoc]

/-- Successful system transfers require an existing receiver and have exactly
the credited transfer state; storage-staking failure is handled by rollback. -/
theorem refund_success_raw (c : ReceiptCtx) (st : ChainState) (amount : Nat)
    (hrefund : c.receipt.isRefund = true) (hactions : c.action.actions = [.transfer amount])
    (hsuccess : (runReceiptActions c st).2 = none) :
    ∃ account, st.account? c.receipt.receiverId = some account ∧
      (runReceiptActions c st).1 =
        { state := refundTransferState c st account amount, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting,
          gasBurnt := refundExecutionGas c amount, gasUsed := refundExecutionGas c amount } := by
  cases ha : st.account? c.receipt.receiverId with
  | none =>
    have hb := refund_receiptActionBody_missing c
      { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } amount hrefund hactions ha
    unfold runReceiptActions at hsuccess
    dsimp only at hsuccess
    rw [hb] at hsuccess
    contradiction
  | some account =>
    have hb := refund_receiptActionBody_run c
      { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } account amount hrefund hactions ha
    refine ⟨account, rfl, ?_⟩
    by_cases hd : storageStakeDeficit c.cfg { account with amount := account.amount + amount } > 0
    all_goals simp only [hd, ↓reduceIte] at hb
    all_goals simp [runReceiptActions, hb]

/-- Successful system refunds credit their backing exactly once, including
current-key allowance restoration, without token burn or new backed receipts. -/
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
  simp only [applyActionReceipt, Exec.commitStorage, hrun, Exec.totalFunds_storageAccounting]
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
