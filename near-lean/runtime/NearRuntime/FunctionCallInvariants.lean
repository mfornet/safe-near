import NearRuntime.MaterializeInvariants

namespace Near
open Wasm Wasm.Near

theorem sum_map_add_nat (items : List α) (f g : α → Nat) :
    (items.map fun item => f item + g item).sum = (items.map f).sum + (items.map g).sum := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

/-- Outgoing gas backing is discharged separately from VM deposit conservation. -/
def functionCallGasFunds (c : ReceiptCtx) (outcome : VMOutcome) : Nat :=
  (outcome.receipts.map fun spec => if c.receipt.receiverId == systemAccount then 0
    else Fees.receiptGasBudget c.cfg (stringOfBytes spec.receiverId)
      (spec.actions.map (actionOfPromiseRaw c.codeOf)) * c.action.gasPrice).sum

theorem materializeFunctionCallRaw_funds_split (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    receiptsFunds c.cfg (materializeFunctionCallRaw c isLast outcome initial).receipts =
      receiptsDeposits outcome.receipts + functionCallGasFunds c outcome := by
  rw [materializeFunctionCallRaw_funds]
  simp [functionCallReceiptValue, functionCallGasFunds,
    Fees.totalDeposit, List.map_map, Function.comp_def, receiptsDeposits, receiptsValue, depositValue]

theorem materializeFunctionCallRaw_totalBalance (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    (materializeFunctionCallRaw c isLast outcome initial).state.totalBalance = initial.totalBalance := by
  have h := congrArg ChainState.totalBalance (materializeFunctionCallRaw_frame c isLast outcome initial)
  simpa only [ChainState.totalBalance, ChainState.withoutIds] using h

/-- Successful validation identifies the exact executable constructor used by commit. -/
theorem functionCallEffects_success (c : ReceiptCtx) (account : Account) (outcome : VMOutcome)
    (isLast : Bool) (state : ChainState) (effects : FunctionCallEffects)
    (h : functionCallEffects c account outcome isLast state = .ok effects) :
    effects = materializeFunctionCallRaw c isLast outcome
      ((state.setAccount c.receipt.receiverId
        { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
          c.receipt.receiverId outcome.storage) :=
  materializeFunctionCall_success c isLast outcome _ effects h

/-- Checked commits change the receiver and id counter, framing the remaining state. -/
theorem commitFunctionCall_frame (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (h : functionCallEffects c account outcome isLast exec.state = .ok effects) :
    (exec.commitFunctionCall outcome effects).state.withoutIds =
      ((exec.state.setAccount c.receipt.receiverId
        { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
          c.receipt.receiverId outcome.storage).withoutIds := by
  change effects.state.withoutIds = _
  rw [functionCallEffects_success c account outcome isLast exec.state effects h]
  exact materializeFunctionCallRaw_frame _ _ _ _

theorem commitFunctionCall_accountsUnique (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects)
    (h : exec.state.AccountsUnique) :
    (exec.commitFunctionCall outcome effects).state.AccountsUnique := by
  have hf := congrArg ChainState.accounts (commitFunctionCall_frame exec c account outcome isLast effects heffects)
  change (exec.commitFunctionCall outcome effects).state.accounts =
    (exec.state.setAccount c.receipt.receiverId
      { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).accounts at hf
  unfold ChainState.AccountsUnique
  rw [hf]
  exact h.setAccount _ _

theorem commitFunctionCall_balance (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects)
    (hwf : exec.state.AccountsUnique) (haccount : exec.state.account? c.receipt.receiverId = some account) :
    (exec.commitFunctionCall outcome effects).state.totalBalance + account.amount =
      exec.state.totalBalance + outcome.balance := by
  have hm := materializeFunctionCallRaw_totalBalance c isLast outcome
    ((exec.state.setAccount c.receipt.receiverId
      { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
      c.receipt.receiverId outcome.storage)
  have ha := exec.state.totalBalance_setAccount c.receipt.receiverId
    { account with amount := outcome.balance, storageUsage := outcome.storageUsage } account hwf haccount
  have he := functionCallEffects_success c account outcome isLast exec.state effects heffects
  change effects.state.totalBalance + account.amount = _
  rw [he]
  dsimp only at ha
  rw [hm]
  change (exec.state.setAccount c.receipt.receiverId
    { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).totalBalance + account.amount = _
  omega

/-- Checked commit retains deposits and the exact outgoing gas purchase price. -/
theorem commitFunctionCall_totalFunds (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects)
    (hwf : exec.state.AccountsUnique) (haccount : exec.state.account? c.receipt.receiverId = some account) :
    (exec.commitFunctionCall outcome effects).totalFunds c.cfg + account.amount =
      exec.totalFunds c.cfg + outcome.balance + receiptsDeposits outcome.receipts + functionCallGasFunds c outcome := by
  have hb := commitFunctionCall_balance exec c account outcome isLast effects heffects hwf haccount
  have he := functionCallEffects_success c account outcome isLast exec.state effects heffects
  unfold Exec.totalFunds
  change effects.state.totalBalance + receiptsFunds c.cfg (exec.newReceipts ++ effects.receipts) + account.amount = _
  rw [receiptsFunds_append, he, materializeFunctionCallRaw_funds_split]
  change effects.state.totalBalance + account.amount = _ at hb
  rw [he] at hb
  omega

/-- The public VM funding theorem discharges the deposit-accounting premise.
`FunctionCallFunding` discharges outgoing gas backing using concrete execution. -/

theorem commitFunctionCall_funded (exec : Exec) (c : ReceiptCtx) (account : Account)
    (code : ContractCode) (method : String) (args : Bytes) (gas deposit : Nat) (isLast : Bool)
    (effects : FunctionCallEffects) (accounting : Option TrieOverlay.State) (hwf : exec.state.AccountsUnique)
    (haccount : exec.state.account? c.receipt.receiverId = some account)
    (hsuccess : (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast accounting)
      (exec.state.contractStorage c.receipt.receiverId)).aborted = none)
    (heffects : functionCallEffects c account
      (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast accounting)
        (exec.state.contractStorage c.receipt.receiverId)) isLast exec.state = .ok effects) :
    let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast accounting)
      (exec.state.contractStorage c.receipt.receiverId)
    (exec.commitFunctionCall outcome effects).totalFunds c.cfg =
      exec.totalFunds c.cfg + deposit + outcome.subsidizedAmount + functionCallGasFunds c outcome := by
  dsimp only
  have hf := run_success_funding c.cfg code.module code.size method
    (functionCallContext c account args gas deposit isLast accounting) (exec.state.contractStorage c.receipt.receiverId)
    defaultFuel hsuccess
  have hc := commitFunctionCall_totalFunds exec c account _ isLast effects heffects hwf haccount
  change (run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast accounting)
    (exec.state.contractStorage c.receipt.receiverId)).balance + _ = account.amount + deposit + _ at hf
  omega

/-- Successful execution supplies the validation witness; no caller-supplied
financial oracle or unsupported-decoder premise is needed. -/
theorem applyFunctionCall_success_funded (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (isLast : Bool) (before after : Exec)
    (hwf : before.state.AccountsUnique)
    (hrun : (applyFunctionCall c method args gas deposit isLast).run.run before = (.ok (), after)) :
    ∃ (account : Account) (code : ContractCode) (effects : FunctionCallEffects),
      before.state.account? c.receipt.receiverId = some account ∧ account.code = some code ∧
      let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast before.storageAccounting)
        (before.state.contractStorage c.receipt.receiverId)
      outcome.aborted = none ∧ functionCallEffects c account outcome isLast before.state = .ok effects ∧
      after = (before.recordVMOutcome outcome).commitFunctionCall outcome effects ∧
      after.totalFunds c.cfg + before.subsidizedAmount = before.totalFunds c.cfg + deposit +
        after.subsidizedAmount + functionCallGasFunds c outcome := by
  rw [applyFunctionCall_run] at hrun
  cases ha : before.state.account? c.receipt.receiverId with
  | none =>
    simp only [ha] at hrun
    have bad := congrArg Prod.fst hrun
    cases bad
  | some account =>
    cases hc : account.code with
    | none =>
      simp only [ha, hc] at hrun
      have bad := congrArg Prod.fst hrun
      cases bad
    | some code =>
      cases hi : code.decodeIssue with
      | some issue =>
        simp only [ha, hc, hi] at hrun
        have bad := congrArg Prod.fst hrun
        cases bad
      | none =>
        let outcome := run c.cfg code.module code.size method (functionCallContext c account args gas deposit isLast before.storageAccounting)
          (before.state.contractStorage c.receipt.receiverId)
        simp only [ha, hc, hi] at hrun
        change ((match outcome.aborted with
          | some error => (.error (.functionCallError error), before.recordVMOutcome outcome)
          | none => match functionCallEffects c account outcome isLast before.state with
            | .error error => (.error error, before.recordVMOutcome outcome)
            | .ok effects => (.ok (), (before.recordVMOutcome outcome).commitFunctionCall outcome effects)) :
            Except RuntimeError Unit × Exec) = (.ok (), after) at hrun
        cases he : outcome.aborted with
        | some error =>
          rw [he] at hrun
          have bad := congrArg Prod.fst hrun
          cases bad
        | none =>
          rw [he] at hrun
          cases hx : functionCallEffects c account outcome isLast before.state with
          | error error =>
            rw [hx] at hrun
            have bad := congrArg Prod.fst hrun
            cases bad
          | ok effects =>
            rw [hx] at hrun
            have heq : (before.recordVMOutcome outcome).commitFunctionCall outcome effects = after :=
              congrArg Prod.snd hrun
            subst after
            refine ⟨account, code, effects, rfl, hc, he, hx, rfl, ?_⟩
            have hf := commitFunctionCall_funded (before.recordVMOutcome outcome) c account code method args gas deposit
              isLast effects before.storageAccounting hwf ha he hx
            change ((before.recordVMOutcome outcome).commitFunctionCall outcome effects).totalFunds c.cfg =
              before.totalFunds c.cfg + deposit + outcome.subsidizedAmount + functionCallGasFunds c outcome at hf
            change ((before.recordVMOutcome outcome).commitFunctionCall outcome effects).totalFunds c.cfg +
              before.subsidizedAmount = before.totalFunds c.cfg + deposit +
                (before.subsidizedAmount + outcome.subsidizedAmount) + functionCallGasFunds c outcome
            omega

theorem applyFunctionCall_success_accountsUnique (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (isLast : Bool) (before after : Exec)
    (hwf : before.state.AccountsUnique)
    (hrun : (applyFunctionCall c method args gas deposit isLast).run.run before = (.ok (), after)) :
    after.state.AccountsUnique := by
  obtain ⟨account, code, effects, ha, hc, he, hx, heq, hf⟩ :=
    applyFunctionCall_success_funded c method args gas deposit isLast before after hwf hrun
  rw [heq]
  exact commitFunctionCall_accountsUnique _ c account _ isLast effects hx hwf

end Near
