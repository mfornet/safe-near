import Skeleton.FailureCosts

/-! Gas bounds for actual storage length rejections, including startup. -/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts MeteredHosts.StorageMetered
set_option maxHeartbeats 800000

private theorem loading_burnsOnly :
    ∀ charge ∈ loadingCharges 0, BurnsOnly charge := by
  simp [loadingCharges, BurnsOnly]

/-- The complete actual rejection burns at most its original startup/body budget. -/
theorem keyFailureOutcome_burnt_le (ctx : Context) (raw : Storage) (rest : Nat)
    (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (keyFailureAttemptBudget ctx raw rest)) :
    (keyFailureOutcome ctx raw).burntGas ≤ keyFailureAttemptBudget ctx raw rest := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := keyFailureBudget cfg (executionStore cfg vm raw) rest
  have hl := applyCharges_credits (vm.toNearState cfg raw) (loadingCharges 0)
    (8 * cfg.wasm.regularOpCost + budget) loading_burnsOnly hcredits
  have hload : (executionLoaded cfg vm raw).gas.burnt =
      burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) := by
    simpa only [executionLoaded, VMContext.toNearState, Nat.zero_add] using hl.2.1
  have hac := GasCounter.burn_credits (executionLoaded cfg vm raw).gas
    (8 * cfg.wasm.regularOpCost) budget (by simpa only [executionLoaded] using hl.2.2.2.2)
  have hactive : (executionActive cfg vm raw).gas.burnt =
      (executionLoaded cfg vm raw).gas.burnt + 8 * cfg.wasm.regularOpCost := by
    simpa only [executionActive, chargeHost] using hac.2.1
  have ha : (executionActive cfg vm raw).gas.Credits budget := by
    simpa only [executionActive, chargeHost] using hac.2.2.2
  have hi : withinLimit (executionStore cfg vm raw).host.config.maxRegisterLen
      (executionStore cfg vm raw).host.context.input.length = true := by
    simp only [executionStore, initialized_host, executionActive_config, executionActive_input]
    change withinLimit (some cfg.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hinput
  have hk := emptyPaid_key ctx raw hp.positive
  rw [StorageFrame.Frame.getMemOrReg (emptyPaid_frame ctx raw)] at hk
  have hv : (keyFailureBefore cfg (executionStore cfg vm raw)).host.context.isView = false :=
    storageInput_isView cfg vm raw
  have hlimit : (keyFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageKeyLen =
      some cfg.wasm.limits.maxLengthStorageKey := by
    have hc := congrArg NearConfig.maxStorageKeyLen (storageInput_config cfg vm raw)
    exact hc
  have hw := wp_save_key_too_long cfg (executionStore cfg vm raw) execLimits
    cfg.wasm.limits.maxLengthStorageKey rest (by rfl) (by rfl) (by rfl) hi hv hk hlimit hlong ha
  obtain ⟨_, hpost, _⟩ := hw.result
  have hb := hw.burnt_le
  rw [hpost.2.1] at hb
  simp only [StepResult.host, atCode, executionStore, initialized_host] at hb
  simp only [keyFailureOutcome, outcomeOfExecution, StepResult.host]
  change (keyFailureStore cfg (executionStore cfg vm raw) _).host.gas.burnt ≤ _
  change (keyFailureStore cfg (executionStore cfg vm raw) _).host.gas.burnt ≤
    (executionActive cfg vm raw).gas.burnt + budget at hb
  change _ ≤ burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + budget)
  dsimp only [cfg, vm, budget] at hload hactive hb ⊢
  omega

/-- The public receipt observation retains the startup-inclusive bound. -/
theorem execOn_key_failure_usedGas_le (ctx : Context) (raw : Storage) (rest : Nat)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (keyFailureAttemptBudget ctx raw rest)) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ keyFailureAttemptBudget ctx raw rest := by
  have hr := run_save_key_too_long_public ctx raw rest hp hinput hlong hcredits
  have hb := keyFailureOutcome_burnt_le ctx raw rest hp hinput hlong hcredits
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change (Near.Boundary.observe ctx raw
    (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas ≤ _
  rw [hmethod, hr, Near.Boundary.observe_usedGas_abort (keyFailureOutcome_fields ctx raw).1]
  exact hb

/-- Matching and gas coverage follow from the single original save-cost bound. -/
theorem execOn_key_failure_bounded
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageKey < 1)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      (modelStep ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  have hc : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (keyFailureAttemptBudget ctx raw 0) := by
    apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
    exact Nat.le_trans (by simpa only [Nat.add_zero] using
      keyFailureAttemptBudget_le_saveEmptyCost ctx raw 0) hgas
  constructor
  · exact execOn_matches_key_too_long gasBound ctx raw st 0 hmethod hp hinput hlong hc
  · exact Nat.le_trans (execOn_key_failure_usedGas_le ctx raw 0 hmethod hp hinput hlong hc)
      (by simpa only [Nat.add_zero] using keyFailureAttemptBudget_le_saveEmptyCost ctx raw 0)

/-- The complete actual rejection burns at most its original startup/body budget. -/
theorem valueFailureOutcome_burnt_le (ctx : Context) (raw : Storage) (rest : Nat)
    (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (valueFailureAttemptBudget ctx raw rest)) :
    (valueFailureOutcome ctx raw).burntGas ≤ valueFailureAttemptBudget ctx raw rest := by
  let cfg := ctx.protocol
  let vm := Near.Boundary.toVMContext ctx
  let budget := valueFailureBudget cfg (executionStore cfg vm raw) rest
  have hl := applyCharges_credits (vm.toNearState cfg raw) (loadingCharges 0)
    (8 * cfg.wasm.regularOpCost + budget) loading_burnsOnly hcredits
  have hload : (executionLoaded cfg vm raw).gas.burnt =
      burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) := by
    simpa only [executionLoaded, VMContext.toNearState, Nat.zero_add] using hl.2.1
  have hac := GasCounter.burn_credits (executionLoaded cfg vm raw).gas
    (8 * cfg.wasm.regularOpCost) budget (by simpa only [executionLoaded] using hl.2.2.2.2)
  have hactive : (executionActive cfg vm raw).gas.burnt =
      (executionLoaded cfg vm raw).gas.burnt + 8 * cfg.wasm.regularOpCost := by
    simpa only [executionActive, chargeHost] using hac.2.1
  have ha : (executionActive cfg vm raw).gas.Credits budget := by
    simpa only [executionActive, chargeHost] using hac.2.2.2
  have hi : withinLimit (executionStore cfg vm raw).host.config.maxRegisterLen
      (executionStore cfg vm raw).host.context.input.length = true := by
    simp only [executionStore, initialized_host, executionActive_config, executionActive_input]
    change withinLimit (some cfg.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hinput
  have hk := emptyPaid_key ctx raw hp.positive
  rw [StorageFrame.Frame.getMemOrReg (emptyPaid_frame ctx raw)] at hk
  have hv : (valueFailureBefore cfg (executionStore cfg vm raw)).host.context.isView = false :=
    storageInput_isView cfg vm raw
  have hlimit : (valueFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageValueLen =
      some cfg.wasm.limits.maxLengthStorageValue := by
    have hc := congrArg NearConfig.maxStorageValueLen (storageInput_config cfg vm raw)
    exact hc
  have hvalue := emptyPaid_value ctx raw
  rw [StorageFrame.Frame.getMemOrReg (emptyPaid_frame ctx raw)] at hvalue
  have hkcfg : (valueFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageKeyLen =
      some cfg.wasm.limits.maxLengthStorageKey := by
    have hc := congrArg NearConfig.maxStorageKeyLen (storageInput_config cfg vm raw)
    exact hc
  have hkaccepted : ∀ n, (valueFailureBefore cfg (executionStore cfg vm raw)).host.config.maxStorageKeyLen =
      some n → 1 ≤ n := by
    intro n hn
    rw [hkcfg] at hn
    cases Option.some.inj hn
    exact hkeyAccepted
  have hw := wp_save_value_too_long cfg (executionStore cfg vm raw) execLimits ctx.args
    cfg.wasm.limits.maxLengthStorageValue rest (by rfl) (by rfl) (by rfl)
    hi hv hk hkaccepted hvalue hlimit hlong ha
  obtain ⟨_, hpost, _⟩ := hw.result
  have hb := hw.burnt_le
  rw [hpost.2.1] at hb
  simp only [StepResult.host, atCode, executionStore, initialized_host] at hb
  simp only [valueFailureOutcome, outcomeOfExecution, StepResult.host]
  change (valueFailureStore cfg (executionStore cfg vm raw) _ _).host.gas.burnt ≤ _
  change (valueFailureStore cfg (executionStore cfg vm raw) _ _).host.gas.burnt ≤
    (executionActive cfg vm raw).gas.burnt + budget at hb
  change _ ≤ burnSum (vm.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + budget)
  dsimp only [cfg, vm, budget] at hload hactive hb ⊢
  omega

/-- The public receipt observation retains the startup-inclusive bound. -/
theorem execOn_value_failure_usedGas_le (ctx : Context) (raw : Storage) (rest : Nat)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (valueFailureAttemptBudget ctx raw rest)) :
    (Near.Boundary.execOn code raw ctx).usedGas ≤ valueFailureAttemptBudget ctx raw rest := by
  have hr := run_save_value_too_long_public ctx raw rest hp hinput hkeyAccepted hlong hcredits
  have hb := valueFailureOutcome_burnt_le ctx raw rest hp hinput hkeyAccepted hlong hcredits
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change (Near.Boundary.observe ctx raw
    (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas ≤ _
  rw [hmethod, hr, Near.Boundary.observe_usedGas_abort (valueFailureOutcome_fields ctx raw).1]
  exact hb

/-- Matching and gas coverage follow from the single original save-cost bound. -/
theorem execOn_value_failure_bounded
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkeyAccepted : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hlong : ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      (modelStep ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ saveEmptyCost ctx := by
  have hc : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (valueFailureAttemptBudget ctx raw 0) := by
    apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
    exact Nat.le_trans (by simpa only [Nat.add_zero] using
      valueFailureAttemptBudget_le_saveEmptyCost ctx raw 0) hgas
  constructor
  · exact execOn_matches_value_too_long gasBound ctx raw st 0 hmethod hp hinput hkeyAccepted hlong hc
  · exact Nat.le_trans (execOn_value_failure_usedGas_le ctx raw 0 hmethod hp hinput hkeyAccepted hlong hc)
      (by simpa only [Nat.add_zero] using valueFailureAttemptBudget_le_saveEmptyCost ctx raw 0)

end WNear.Skeleton
