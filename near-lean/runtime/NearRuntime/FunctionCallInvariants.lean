import NearRuntime.MaterializeInvariants

namespace Near
open Wasm Wasm.Near

/-- Funds reserved in outgoing gas budgets. They are not new deposits: the
receipt-wide conservation proof must discharge them against VM gas reservation. -/
def functionCallGasFunds (c : ReceiptCtx) (outcome : VMOutcome) : Nat :=
  (outcome.receipts.map fun spec => if c.receipt.receiverId == systemAccount then 0
    else Fees.receiptGasBudget c.cfg (stringOfBytes spec.receiverId)
      (spec.actions.map (actionOfPromise c.codeOf)) * c.action.gasPrice).sum

theorem materializeFunctionCall_funds_split (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    receiptsFunds c.cfg (materializeFunctionCall c isLast outcome initial).receipts =
      receiptsDeposits outcome.receipts + functionCallGasFunds c outcome := by
  rw [materializeFunctionCall_funds]
  simp [functionCallReceiptValue, functionCallGasFunds, List.sum_map_add,
    Fees.totalDeposit, List.map_map, Function.comp_def, receiptsDeposits, receiptsValue, depositValue]

theorem materializeFunctionCall_totalBalance (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    (materializeFunctionCall c isLast outcome initial).state.totalBalance = initial.totalBalance := by
  have h := congrArg ChainState.totalBalance (materializeFunctionCall_frame c isLast outcome initial)
  simpa only [ChainState.totalBalance, ChainState.withoutIds] using h

/-- Successful commit changes receiver balance/storage and allocates ids;
all remaining chain fields, including delayed and postponed work, are framed. -/
theorem commitFunctionCall_frame (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) :
    (exec.commitFunctionCall c account outcome isLast).state.withoutIds =
      ((exec.state.setAccount c.receipt.receiverId
        { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
          c.receipt.receiverId outcome.storage).withoutIds :=
  materializeFunctionCall_frame c isLast outcome _

theorem commitFunctionCall_accountsUnique (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (h : exec.state.AccountsUnique) :
    (exec.commitFunctionCall c account outcome isLast).state.AccountsUnique := by
  have hf := congrArg ChainState.accounts (commitFunctionCall_frame exec c account outcome isLast)
  change (exec.commitFunctionCall c account outcome isLast).state.accounts =
    (exec.state.setAccount c.receipt.receiverId
      { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).accounts at hf
  unfold ChainState.AccountsUnique
  rw [hf]
  exact h.setAccount _ _

theorem commitFunctionCall_balance (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (hwf : exec.state.AccountsUnique)
    (haccount : exec.state.account? c.receipt.receiverId = some account) :
    (exec.commitFunctionCall c account outcome isLast).state.totalBalance + account.amount =
      exec.state.totalBalance + outcome.balance := by
  have hm := materializeFunctionCall_totalBalance c isLast outcome
    ((exec.state.setAccount c.receipt.receiverId
      { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
      c.receipt.receiverId outcome.storage)
  have ha := exec.state.totalBalance_setAccount c.receipt.receiverId
    { account with amount := outcome.balance, storageUsage := outcome.storageUsage } account hwf haccount
  change (exec.commitFunctionCall c account outcome isLast).state.totalBalance =
    (exec.state.setAccount c.receipt.receiverId
      { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).totalBalance at hm
  dsimp only at ha
  omega

/-- Commit accounting includes both deposit backing and purchased outgoing gas. -/
theorem commitFunctionCall_totalFunds (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (hwf : exec.state.AccountsUnique)
    (haccount : exec.state.account? c.receipt.receiverId = some account) :
    (exec.commitFunctionCall c account outcome isLast).totalFunds c.cfg + account.amount =
      exec.totalFunds c.cfg + outcome.balance + receiptsDeposits outcome.receipts + functionCallGasFunds c outcome := by
  have hb := commitFunctionCall_balance exec c account outcome isLast hwf haccount
  unfold Exec.totalFunds
  change (exec.commitFunctionCall c account outcome isLast).state.totalBalance +
    receiptsFunds c.cfg (exec.newReceipts ++ _) + account.amount = _
  rw [receiptsFunds_append, materializeFunctionCall_funds_split]
  omega

/-- The public VM funding theorem discharges the deposit-accounting premise.
Only outgoing gas backing remains to connect to receipt-wide gas settlement. -/
theorem commitFunctionCall_funded (exec : Exec) (c : ReceiptCtx) (account : Account)
    (code : ContractCode) (method : String) (args : Bytes) (gas deposit : Nat) (isLast : Bool)
    (hwf : exec.state.AccountsUnique) (haccount : exec.state.account? c.receipt.receiverId = some account)
    (hsuccess : (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast)
      (exec.state.contractStorage c.receipt.receiverId)).aborted = none) :
    let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast)
      (exec.state.contractStorage c.receipt.receiverId)
    (exec.commitFunctionCall c account outcome isLast).totalFunds c.cfg =
      exec.totalFunds c.cfg + deposit + outcome.subsidizedAmount + functionCallGasFunds c outcome := by
  dsimp only
  let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast)
    (exec.state.contractStorage c.receipt.receiverId)
  have hf := run_success_funding c.cfg code.module code.size method
    (functionCallContext c account args gas deposit isLast) (exec.state.contractStorage c.receipt.receiverId)
    defaultFuel hsuccess
  have hc := commitFunctionCall_totalFunds exec c account
    (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast)
      (exec.state.contractStorage c.receipt.receiverId)) isLast hwf haccount
  change outcome.balance + receiptsDeposits outcome.receipts = account.amount + deposit + outcome.subsidizedAmount at hf
  dsimp only [outcome] at hf
  omega

/-- Actual successful function-call execution has no unexplained ledger delta.
The witness identifies the account, deployed code and public VM result used by
execution; no financial oracle is supplied by the caller. -/
theorem applyFunctionCall_success_funded (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (isLast : Bool) (before after : Exec)
    (hwf : before.state.AccountsUnique)
    (hrun : (applyFunctionCall c method args gas deposit isLast).run.run before = (.ok (), after)) :
    ∃ (account : Account) (code : ContractCode),
      before.state.account? c.receipt.receiverId = some account ∧ account.code = some code ∧
      let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast)
        (before.state.contractStorage c.receipt.receiverId)
      outcome.aborted = none ∧
      after = (before.recordVMOutcome outcome).commitFunctionCall c account outcome isLast ∧
      after.totalFunds c.cfg + before.subsidizedAmount = before.totalFunds c.cfg + deposit +
        after.subsidizedAmount + functionCallGasFunds c outcome := by
  rw [applyFunctionCall_run] at hrun
  cases ha : before.state.account? c.receipt.receiverId with
  | none =>
    simp only [ha] at hrun
    have hbad := congrArg Prod.fst hrun
    cases hbad
  | some account =>
    cases hc : account.code with
    | none =>
      simp only [ha, hc] at hrun
      have hbad := congrArg Prod.fst hrun
      cases hbad
    | some code =>
      let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast)
        (before.state.contractStorage c.receipt.receiverId)
      simp only [ha, hc] at hrun
      change ((match outcome.aborted with
        | some error => (.error (.functionCallError error), before.recordVMOutcome outcome)
        | none => (.ok (), (before.recordVMOutcome outcome).commitFunctionCall c account outcome isLast)) :
          Except RuntimeError Unit × Exec) = (.ok (), after) at hrun
      cases he : outcome.aborted with
      | some error =>
        rw [he] at hrun
        have hbad := congrArg Prod.fst hrun
        cases hbad
      | none =>
        rw [he] at hrun
        have heq : (before.recordVMOutcome outcome).commitFunctionCall c account outcome isLast = after :=
          congrArg Prod.snd hrun
        subst after
        refine ⟨account, code, rfl, hc, he, rfl, ?_⟩
        have hf := commitFunctionCall_funded (before.recordVMOutcome outcome) c account code method args
          gas deposit isLast hwf ha he
        change ((before.recordVMOutcome outcome).commitFunctionCall c account outcome isLast).totalFunds c.cfg =
          before.totalFunds c.cfg + deposit + outcome.subsidizedAmount + functionCallGasFunds c outcome at hf
        change ((before.recordVMOutcome outcome).commitFunctionCall c account outcome isLast).totalFunds c.cfg +
          before.subsidizedAmount = before.totalFunds c.cfg + deposit +
            (before.subsidizedAmount + outcome.subsidizedAmount) + functionCallGasFunds c outcome
        omega

theorem applyFunctionCall_success_accountsUnique (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (isLast : Bool) (before after : Exec)
    (hwf : before.state.AccountsUnique)
    (hrun : (applyFunctionCall c method args gas deposit isLast).run.run before = (.ok (), after)) :
    after.state.AccountsUnique := by
  obtain ⟨account, code, _, _, _, heq, _⟩ :=
    applyFunctionCall_success_funded c method args gas deposit isLast before after hwf hrun
  rw [heq]
  exact commitFunctionCall_accountsUnique _ _ _ _ _ hwf

end Near
