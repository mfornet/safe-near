import NearRuntime.Apply
import NearRuntime.NewActionRun

namespace Near
open Wasm.Near

/-- Incremental accounting before receipt finalization: function-call burn is
part of total burn, total burn is part of gas used, and use fits the action budget. -/
structure GasDelta (budget : Nat) (before after : Exec) : Prop where
  functionCall_mono : before.gasBurntForFunctionCall ≤ after.gasBurntForFunctionCall
  burnt_mono : before.gasBurnt ≤ after.gasBurnt
  used_mono : before.gasUsed ≤ after.gasUsed
  functionCall_le_burnt : after.gasBurntForFunctionCall + before.gasBurnt ≤ before.gasBurntForFunctionCall + after.gasBurnt
  burnt_le_used : after.gasBurnt + before.gasUsed ≤ before.gasBurnt + after.gasUsed
  budget_bound : after.gasUsed ≤ before.gasUsed + budget

namespace GasDelta

theorem of_fields (before after : Exec) (budget : Nat)
    (hfc : after.gasBurntForFunctionCall = before.gasBurntForFunctionCall)
    (hb : after.gasBurnt = before.gasBurnt) (hu : after.gasUsed = before.gasUsed) :
    GasDelta budget before after := by
  constructor <;> omega

theorem mono {before after : Exec} {budget larger : Nat} (h : GasDelta budget before after)
    (hle : budget ≤ larger) : GasDelta larger before after := by
  rcases h with ⟨hfc, hb, hu, hfb, hbu, hbudget⟩
  constructor <;> omega

theorem trans {before middle after : Exec} {first second : Nat}
    (hfirst : GasDelta first before middle) (hsecond : GasDelta second middle after) :
    GasDelta (first + second) before after := by
  rcases hfirst with ⟨hf1, hb1, hu1, hfb1, hbu1, hg1⟩
  rcases hsecond with ⟨hf2, hb2, hu2, hfb2, hbu2, hg2⟩
  constructor <;> omega

end GasDelta

/-- A budget bound on both successful and failed executions of a receipt operation. -/
def ExecM.GasBound (operation : ExecM α) (budget : Nat) : Prop :=
  ∀ before, GasDelta budget before (operation.run.run before).2

theorem ExecM.GasBound.bind {operation : ExecM α} {next : α → ExecM β} {first second : Nat}
    (hfirst : operation.GasBound first) (hsecond : ∀ value, (next value).GasBound second) :
    (operation >>= next).GasBound (first + second) := by
  intro before
  rw [execM_run_bind]
  have hp := hfirst before
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => exact hp.mono (Nat.le_add_right first second)
    | ok value => exact hp.trans (hsecond value middle)

theorem gasBound_pure (value : α) : (pure value : ExecM α).GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_throw (error : RuntimeError) : (throw error : ExecM α).GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_modify (f : Exec → Exec) (budget : Nat) (h : ∀ before, GasDelta budget before (f before)) :
    (modify f : ExecM Unit).GasBound budget := by
  intro before
  exact h before

theorem gasBound_burnGas (n : Nat) : (burnGas n).GasBound n := by
  intro before
  change GasDelta n before { before with gasBurnt := before.gasBurnt + n, gasUsed := before.gasUsed + n }
  constructor <;> dsimp only <;> omega

theorem gasBound_useGas (n : Nat) : (useGas n).GasBound n := by
  intro before
  change GasDelta n before { before with gasUsed := before.gasUsed + n }
  constructor <;> dsimp only <;> omega

/-- Recording a bounded public VM result spends at most its attached gas. -/
theorem recordVMOutcome_gasDelta (before : Exec) (outcome : VMOutcome) (budget : Nat)
    (horder : outcome.burntGas ≤ outcome.usedGas) (hbudget : outcome.usedGas ≤ budget) :
    GasDelta budget before (before.recordVMOutcome outcome) := by
  constructor <;> dsimp only [Exec.recordVMOutcome] <;> omega

/-- State, storage and promise materialization have no gas effects. -/
theorem commitFunctionCall_gasDelta (before : Exec) (outcome : VMOutcome) (effects : FunctionCallEffects) :
    GasDelta 0 before (before.commitFunctionCall outcome effects) :=
  GasDelta.of_fields _ _ _ rfl rfl rfl

/-- A small executable unfolding rule, keeping VM execution abstract. -/
theorem applyFunctionCall_run (c : ReceiptCtx) (method : String) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) (before : Exec) :
    (applyFunctionCall c method args gas deposit isLast).run.run before =
      match before.state.account? c.receipt.receiverId with
      | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
      | some account => match resolveContract before.state account with
        | none => (.error (.functionCallError (.compilationError "CodeDoesNotExist")), before)
        | some code => match code.decodeIssue with
          | some issue => (.error (.executionIssue issue), before)
          | none =>
          let outcome := run c.cfg code.module code.size method
            (functionCallContext c account args gas deposit isLast before.storageAccounting)
            (before.state.contractStorage c.receipt.receiverId)
          let charged := before.recordVMOutcome outcome
          match outcome.aborted with
          | some error => (.error (.functionCallError error), charged)
          | none => match functionCallEffects c account outcome isLast before.state with
            | .error error => (.error error, charged)
            | .ok effects => (.ok (), charged.commitFunctionCall outcome effects) := by
  cases ha : before.state.account? c.receipt.receiverId with
  | none => simp [-StateT.run_bind, applyFunctionCall, getAccount, getState, ha]
  | some account =>
    cases hc : resolveContract before.state account with
    | none => simp [-StateT.run_bind, applyFunctionCall, getAccount, getState, ha, hc]
    | some code =>
      cases hi : code.decodeIssue with
      | some issue => simp [-StateT.run_bind, applyFunctionCall, getAccount, getState, ha, hc, hi]
      | none =>
        cases he : (run c.cfg code.module code.size method
          (functionCallContext c account args gas deposit isLast before.storageAccounting)
          (before.state.contractStorage c.receipt.receiverId)).aborted <;>
          cases hf : functionCallEffects c account
            (run c.cfg code.module code.size method
              (functionCallContext c account args gas deposit isLast before.storageAccounting)
              (before.state.contractStorage c.receipt.receiverId)) isLast before.state <;>
          simp [-StateT.run_bind, applyFunctionCall, getAccount, getState, ha, hc, hi, he, hf]

/-- Each function-call action spends at most its own attached gas, on every exit. -/
theorem applyFunctionCall_gasBound (c : ReceiptCtx) (method : String) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) : (applyFunctionCall c method args gas deposit isLast).GasBound gas := by
  intro before
  rw [applyFunctionCall_run]
  split
  · exact GasDelta.of_fields _ _ _ rfl rfl rfl
  · rename_i account haccount
    split
    · exact GasDelta.of_fields _ _ _ rfl rfl rfl
    · rename_i code hcode
      split
      · exact GasDelta.of_fields _ _ _ rfl rfl rfl
      · have hv := run_gas_bounded c.cfg code.module code.size method
          (functionCallContext c account args gas deposit isLast before.storageAccounting)
          (before.state.contractStorage c.receipt.receiverId)
          (fuelFor c.cfg code.module (functionCallContext c account args gas deposit isLast before.storageAccounting))
        have hc := recordVMOutcome_gasDelta before _ gas hv.1 hv.2.1
        dsimp only
        split
        · exact hc
        · split
          · exact hc
          · simpa only [Nat.add_zero] using hc.trans (commitFunctionCall_gasDelta _ _ _)

theorem gasBound_bind_zero {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.GasBound 0) (hnext : ∀ value, (next value).GasBound 0) :
    (operation >>= next).GasBound 0 := hfirst.bind hnext

theorem gasBound_get : (get : ExecM Exec).GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_getState : getState.GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_modifyState (f : ChainState → ChainState) : (modifyState f).GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_putAccount (id : AccountId) (account : Account) : (putAccount id account).GasBound 0 :=
  gasBound_modifyState _

theorem gasBound_emit (receipt : Receipt) : (emit receipt).GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_getAccount (id : AccountId) : (getAccount id).GasBound 0 := by
  unfold getAccount
  apply gasBound_bind_zero gasBound_getState
  intro st
  split
  · exact gasBound_pure _
  · exact gasBound_throw _

theorem ExecM.GasBound.mono {operation : ExecM α} {budget larger : Nat}
    (h : operation.GasBound budget) (hle : budget ≤ larger) : operation.GasBound larger :=
  fun before => (h before).mono hle

theorem gasBound_fresh : (fresh : ExecM Nat).GasBound 0 := by
  intro before
  exact GasDelta.of_fields _ _ _ rfl rfl rfl

theorem gasBound_liftExcept (e : Except RuntimeError α) : (liftExcept e).GasBound 0 := by
  cases e
  · exact gasBound_throw _
  · exact gasBound_pure _

theorem gasBound_burnAction (amount : Nat) : (modify (·.burnAction amount) : ExecM Unit).GasBound 0 :=
  gasBound_modify _ _ (fun _ => GasDelta.of_fields _ _ _ rfl rfl rfl)

/-- The bookkeeping of a deployed global contract spends no gas. -/
theorem gasBound_applyDeployGlobalContract (c : ReceiptCtx) (code : ContractCode) (mode : GlobalDeployMode) :
    (applyDeployGlobalContract c code mode).GasBound 0 := by
  unfold applyDeployGlobalContract
  repeat (first
    | exact gasBound_pure _
    | exact gasBound_throw _
    | exact gasBound_getState
    | exact gasBound_getAccount _
    | exact gasBound_putAccount _ _
    | exact gasBound_modifyState _
    | exact gasBound_emit _
    | exact gasBound_fresh
    | exact gasBound_liftExcept _
    | exact gasBound_burnAction _
    | (refine gasBound_bind_zero ?_ (fun value => ?_)))

/-- A delegate action spends exactly what the relayer prepaid for the receipt it creates. -/
theorem gasBound_applyDelegateAction (c : ReceiptCtx) (act : Action) :
    (applyDelegateAction c act).GasBound
      (act.attachedGas + Fees.nestedExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts act
        + Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts act) := by
  have hrequired : delegateRequired c act ≤
      act.attachedGas + Fees.nestedExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts act := by
    cases act <;> simp [delegateRequired, Action.attachedGas, Fees.nestedExec, Fees.attachedGasList_eq] <;> omega
  unfold applyDelegateAction
  have h : (liftExcept (delegateChecks c act) >>= fun _ => getState >>= fun st =>
      liftExcept (delegateState c st act) >>= fun moved => modifyState (fun _ => moved) >>= fun _ =>
      useGas (delegateRequired c act) >>= fun _ =>
      burnGas (Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts act) >>= fun _ =>
      fresh >>= fun id => emit (delegateReceipt c act id)).GasBound
      (0 + (0 + (0 + (0 + ((delegateRequired c act) + ((Fees.prepaidSend c.cfg.fees.actionFees
        c.cfg.wasm.ethImplicitAccounts act) + (0 + 0))))))) := by
    refine ExecM.GasBound.bind (gasBound_liftExcept _) (fun _ => ?_)
    refine ExecM.GasBound.bind gasBound_getState (fun st => ?_)
    refine ExecM.GasBound.bind (gasBound_liftExcept _) (fun moved => ?_)
    refine ExecM.GasBound.bind (gasBound_modifyState _) (fun _ => ?_)
    refine ExecM.GasBound.bind (gasBound_useGas _) (fun _ => ?_)
    refine ExecM.GasBound.bind (gasBound_burnGas _) (fun _ => ?_)
    refine ExecM.GasBound.bind gasBound_fresh (fun id => ?_)
    exact gasBound_emit _
  refine ExecM.GasBound.mono h ?_
  omega

set_option maxHeartbeats 2000000 in
/-- Every action body is bounded by its attached function-call gas. -/
theorem applyAction_gasBound_plain (c : ReceiptCtx) (isLast : Bool) (action : Action)
    (hd : ∀ s r a n i m k sig v, action ≠ .delegate s r a n i m k sig v) :
    (applyAction c isLast action).GasBound action.attachedGas := by
  cases action with
  | functionCall method args gas deposit => exact applyFunctionCall_gasBound c method args gas deposit isLast
  | delegate s r a n i m k sig v => exact absurd rfl (hd s r a n i m k sig v)
  | deployGlobalContract code mode =>
    exact ExecM.GasBound.mono (gasBound_applyDeployGlobalContract c code mode) (Nat.zero_le _)
  | _ =>
    dsimp only [applyAction]
    repeat (first
      | contradiction
      | exact gasBound_pure _
      | exact gasBound_throw _
      | exact gasBound_get
      | exact gasBound_getState
      | exact gasBound_getAccount _
      | exact gasBound_putAccount _ _
      | exact gasBound_modifyState _
      | exact gasBound_emit _
      | exact gasBound_fresh
      | exact gasBound_liftExcept _
      | exact gasBound_burnAction _
      | (refine gasBound_bind_zero ?_ (fun value => ?_))
      | (apply gasBound_modify; intro before; exact GasDelta.of_fields _ _ _ rfl rfl rfl)
      | split)

/-- Every action body is bounded by its attached gas plus what a delegate action prepays. -/
theorem applyAction_gasBound (c : ReceiptCtx) (isLast : Bool) (action : Action) :
    (applyAction c isLast action).GasBound
      (action.attachedGas + Fees.nestedExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts action
        + Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts action) := by
  cases action with
  | delegate s r a n i m k sig v =>
    exact gasBound_applyDelegateAction c (.delegate s r a n i m k sig v)
  | _ =>
    refine ExecM.GasBound.mono (applyAction_gasBound_plain c isLast _ ?_) ?_
    · intros; simp
    · simp [Fees.nestedExec, Fees.prepaidSend]

theorem gasBound_bind_left_zero {operation : ExecM α} {next : α → ExecM β} {budget : Nat}
    (hfirst : operation.GasBound 0) (hnext : ∀ value, (next value).GasBound budget) :
    (operation >>= next).GasBound budget := by
  simpa only [Nat.zero_add] using hfirst.bind hnext

theorem gasBound_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).GasBound 0 := by
  unfold checkReceiptAction
  repeat (first
    | exact gasBound_pure _
    | exact gasBound_throw _
    | exact gasBound_get
    | exact gasBound_getState
    | (refine gasBound_bind_zero ?_ (fun value => ?_))
    | split)

theorem gasBound_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).GasBound 0 := by
  unfold checkStorageStake
  repeat (first
    | exact gasBound_pure _
    | exact gasBound_throw _
    | exact gasBound_getState
    | (refine gasBound_bind_zero ?_ (fun value => ?_))
    | split
    | (dsimp only; split))

/-- Recorded execution fees fit the same uniform receipt gas budget. -/
theorem gasBound_fee (isRefund : Bool) (fee : Nat) :
    (chargeReceiptFee isRefund fee).GasBound fee := gasBound_burnGas fee

/-- One action is backed by its protocol execution fee, attached gas and, for a delegate action,
the fees it prepays for the receipt it creates. -/
theorem runReceiptAction_gasBound (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).GasBound
      (Fees.prepaidExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId action
        + action.attachedGas + Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts action) := by
  unfold runReceiptAction
  refine ExecM.GasBound.mono (ExecM.GasBound.bind (gasBound_fee _ _) (fun _ =>
    gasBound_bind_left_zero (gasBound_checkReceiptAction c onlyAction action)
      (fun _ => applyAction_gasBound c isLast action))) ?_
  rw [Fees.prepaidExec_eq]
  omega

/-- Changing only VM randomness leaves the purchased gas bound unchanged;
invalid exact context returns a model issue without spending gas. -/
theorem runReceiptActionAt_gasBound (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) (index : Nat) :
    (runReceiptActionAt c onlyAction isLast action index).GasBound
      (Fees.prepaidExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId action
        + action.attachedGas + Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts action) := by
  cases action <;> try exact runReceiptAction_gasBound c onlyAction isLast _
  cases he : actionRandomSeed c index <;> simp only [runReceiptActionAt, he]
  · exact (gasBound_throw _).mono (Nat.zero_le _)
  · exact runReceiptAction_gasBound _ onlyAction isLast _

/-- The ordered action list consumes at most the sum of its individual budgets,
including an early error that stops the remaining actions. -/
theorem runReceiptActionList_gasBound (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) (index : Nat) :
    (runReceiptActionList c onlyAction actions index).GasBound
      ((actions.map (Fees.prepaidExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId)).sum
        + Fees.totalPrepaid actions
        + Fees.totalPrepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts actions) := by
  induction actions generalizing index with
  | nil => exact gasBound_pure _
  | cons action rest ih =>
    have hm : (modify fun e : Exec => { e with failureIndex := some index } : ExecM Unit).GasBound 0 :=
      gasBound_modify _ _ (fun _ => GasDelta.of_fields _ _ _ rfl rfl rfl)
    have h := gasBound_bind_left_zero hm (fun _ =>
      (runReceiptActionAt_gasBound c onlyAction rest.isEmpty action index).bind (fun _ => ih (index + 1)))
    simpa [runReceiptActionList, Fees.totalPrepaid, Fees.totalPrepaidSend, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- The complete executable action attempt fits the purchased receipt budget. -/
theorem receiptActionBody_gasBound (c : ReceiptCtx) :
    (receiptActionBody c).GasBound (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) := by
  have hbudget : Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions =
      c.cfg.fees.actionFees.newActionReceipt.execution
        + ((c.action.actions.map (Fees.prepaidExec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId)).sum
          + Fees.totalPrepaid c.action.actions
          + Fees.totalPrepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.action.actions) := by
    unfold Fees.receiptGasBudget
    omega
  rw [hbudget]
  unfold receiptActionBody
  refine ExecM.GasBound.bind (gasBound_fee _ _) (fun _ => ?_)
  have h := (runReceiptActionList_gasBound c (c.action.actions.length == 1) c.action.actions 0).bind
    (fun _ => gasBound_bind_left_zero
      (gasBound_modify (fun e : Exec => { e with failureIndex := none }) 0
        (fun _ => GasDelta.of_fields _ _ _ rfl rfl rfl))
      (fun _ => gasBound_checkStorageStake c.cfg c.receipt.receiverId))
  simpa only [Nat.add_zero] using h

/-- Gas premises for receipt accounting follow from execution, for every action
list and every success/error path. -/
theorem runReceiptActions_gas_bounds (c : ReceiptCtx) (st : ChainState) :
    let raw := (runReceiptActions c st).1
    raw.gasBurntForFunctionCall ≤ raw.gasBurnt ∧ raw.gasBurnt ≤ raw.gasUsed ∧
      raw.gasUsed ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions := by
  have h := receiptActionBody_gasBound c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting }
  unfold runReceiptActions
  dsimp only
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw =>
    rw [he] at h
    have hf : raw.gasBurntForFunctionCall ≤ raw.gasBurnt := by
      have hp := h.functionCall_le_burnt
      simpa using hp
    have hb : raw.gasBurnt ≤ raw.gasUsed := by
      have hp := h.burnt_le_used
      simpa using hp
    have hu : raw.gasUsed ≤ Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions := by
      have hp := h.budget_bound
      simpa using hp
    cases result with
    | error error => exact ⟨hf, hb, hu⟩
    | ok value => cases value; exact ⟨hf, hb, hu⟩

end Near
