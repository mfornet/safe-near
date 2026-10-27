import Skeleton.Execution
import Skeleton.InputFailure
import Skeleton.Fuel
import Skeleton.Model
import Skeleton.Costs
import NearRuntime.Refinement
import NearRuntime.InitialCredits

/-!
# Early input failure through actual VM startup

The local two-instruction contract is lifted through loading, entry activation
and the public VM call. Fresh error markers are derived from actual initial
state construction, rather than assumed about an arbitrary host post-state.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- Preparation obligations shared by the success and failure paths. -/
structure PreparationLimits (cfg : RuntimeConfig) : Prop where
  positive : 0 < cfg.wasm.limits.initialMemoryPages
  minmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages
  maximum : cfg.wasm.limits.maxMemoryPages ≤ 65536
  types : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n
  functions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n

def inputFailureAttemptBudget (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : Storage) (rest : Nat) : Nat :=
  MeteredHosts.burnSum (ctx.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + inputFailureBudget cfg.wasm (executionStore cfg ctx raw) rest)

private theorem loading_burnsOnly :
    ∀ charge ∈ loadingCharges 0, MeteredHosts.BurnsOnly charge := by
  simp [loadingCharges, MeteredHosts.BurnsOnly]

/-- Actual loading and activation retain the initial fresh error markers and
empty log list, even before any sufficient-gas assumption is used. -/
theorem executionActive_fresh (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (executionActive cfg ctx raw).lastError = none ∧
    (executionActive cfg ctx raw).lastExecutionIssue = none ∧
    (executionActive cfg ctx raw).logs = [] := by
  have hf := congrArg (fun host : NearState => (host.lastError, host.lastExecutionIssue, host.logs))
    (MeteredHosts.applyCharges_frame (ctx.toNearState cfg raw) (loadingCharges 0) loading_burnsOnly)
  simpa only [executionActive, executionLoaded, chargeHost, VMContext.toNearState,
    Prod.mk.injEq] using hf

/-- Actual VM attempt reaches the early input trap with no execution or
classification premises about a completed method. -/
theorem runAttempt_save_input_too_long (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : Storage) (fuel rest : Nat) (hprepare : PreparationLimits cfg)
    (hfuel : 2 ≤ fuel)
    (hinput : cfg.wasm.limits.maxRegisterSize < ctx.input.length)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits (inputFailureAttemptBudget cfg ctx raw rest)) :
    runAttempt cfg module 0 "save" ctx raw fuel =
      outcomeOfExecution ctx raw (.trap (.host "input: register size exceeded")
        (inputFailureStore cfg.wasm (executionStore cfg ctx raw))) none := by
  let budget := inputFailureBudget cfg.wasm (executionStore cfg ctx raw) rest
  have hs : runAttempt cfg module 0 "save" ctx raw fuel =
      (let result := runInitialized cfg.wasm fuel (.next (entryConfig cfg (executionLoaded cfg ctx raw)))
       outcomeOfExecution ctx raw result.1 result.2) ∧
      (executionLoaded cfg ctx raw).gas.Credits (8 * cfg.wasm.regularOpCost + budget) := by
    simpa only [executionLoaded] using runAttempt_save_credits cfg ctx raw fuel
      (8 * cfg.wasm.regularOpCost + budget) hprepare.positive hprepare.minmax hprepare.maximum
      hprepare.types hprepare.functions hcredits
  have ha : (executionActive cfg ctx raw).gas.Credits budget := by
    have hc := GasCounter.burn_credits (executionLoaded cfg ctx raw).gas
      (8 * cfg.wasm.regularOpCost) budget hs.2
    simpa only [executionActive, chargeHost] using hc.2.2.2
  have hlimit : withinLimit (executionStore cfg ctx raw).host.config.maxRegisterLen
      (executionStore cfg ctx raw).host.context.input.length = false := by
    simp only [executionStore, initialized_host, executionActive_config, executionActive_input]
    simp [VMContext.toNearState, withinLimit, Nat.not_le_of_gt hinput]
  have hr := run_save_input_too_long cfg (executionStore cfg ctx raw) execLimits rest
    (by rfl) (by rfl) hlimit ha
  change runMetered cfg.wasm 2 (.next (entryConfig cfg (executionActive cfg ctx raw))) = _ at hr
  have hextra := runMetered_extra_fuel cfg.wasm 2
    (.next (entryConfig cfg (executionActive cfg ctx raw))) (by rw [hr]; simp) (fuel - 2)
  rw [show 2 + (fuel - 2) = fuel by omega] at hextra
  have hrun := hextra.trans hr
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg ctx raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

/-- The resulting VM abort is the expected guest panic. Fresh markers follow
from startup, and all later host calls are absent from this proof. -/
theorem runAttempt_input_abort (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (fuel rest : Nat) (hprepare : PreparationLimits cfg) (hfuel : 2 ≤ fuel)
    (hinput : cfg.wasm.limits.maxRegisterSize < ctx.input.length)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits (inputFailureAttemptBudget cfg ctx raw rest)) :
    (runAttempt cfg module 0 "save" ctx raw fuel).aborted =
      some (.hostError (.guestPanic "input: register size exceeded")) := by
  rw [runAttempt_save_input_too_long cfg ctx raw fuel rest hprepare hfuel hinput hcredits]
  exact inputFailure_outcome cfg.wasm ctx raw (executionStore cfg ctx raw)
    (executionActive_fresh cfg ctx raw).1 (executionActive_fresh cfg ctx raw).2.1

/-- The exact failed attempt outcome, before the redundant receipt check. -/
def inputFailureOutcome (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) : VMOutcome :=
  outcomeOfExecution ctx raw (.trap (.host "input: register size exceeded")
    (inputFailureStore cfg.wasm (executionStore cfg ctx raw))) none

/-- Startup and the failing input call produce a valid empty receipt graph,
no logs, and the expected panic. -/
theorem inputFailureOutcome_fields (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (inputFailureOutcome cfg ctx raw).aborted =
      some (.hostError (.guestPanic "input: register size exceeded")) ∧
    (inputFailureOutcome cfg ctx raw).logs = [] ∧
    (inputFailureOutcome cfg ctx raw).receiptsValid = true := by
  have hf := executionActive_fresh cfg ctx raw
  have he := inputFailure_error cfg.wasm (executionStore cfg ctx raw) hf.1 hf.2.1
  have hl := (inputFailureStore_frame cfg.wasm (executionStore cfg ctx raw)).2.2.1
  have hz : (inputFailureStore cfg.wasm (executionStore cfg ctx raw)).host.logs = [] :=
    hl.trans hf.2.2
  simp [inputFailureOutcome, outcomeOfExecution, StepResult.host, he, logsOf, hz,
    VMOutcome.receiptsValid, receiptsValidFrom]

/-- The public VM runner's receipt check retains this failure unchanged. -/
theorem run_save_input_too_long_public (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (rest : Nat) (hprepare : PreparationLimits cfg)
    (hinput : cfg.wasm.limits.maxRegisterSize < ctx.input.length)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits (inputFailureAttemptBudget cfg ctx raw rest)) :
    run cfg module 0 "save" ctx raw = inputFailureOutcome cfg ctx raw := by
  have hr := runAttempt_save_input_too_long cfg ctx raw (fuelFor cfg module ctx) rest hprepare
    (Nat.le_trans (by decide : 2 ≤ 16) (fuelFor_save cfg ctx)) hinput hcredits
  simp only [run, hr]
  change (inputFailureOutcome cfg ctx raw).checkReceipts ctx.accountBalance ctx.storageUsage raw = _
  simp only [VMOutcome.checkReceipts, (inputFailureOutcome_fields cfg ctx raw).2.2, ↓reduceIte]

/-- The model rejects an oversized input before inspecting the storage state. -/
theorem modelStep_input_too_long (ctx : NearInterface.Context) (st : Option Storage)
    (hinput : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length) :
    modelStep ctx st () = .error ⟨.panic (.panic "input: register size exceeded"), []⟩ := by
  simp [modelStep, hinput]

/-- One genuine receipt-level model-matching branch, for arbitrary represented
state and raw storage. The failure rolls account effects back at the boundary. -/
theorem execOn_matches_input_too_long
    (gasBound : NearInterface.Context → Option Storage → Unit → Nat)
    (ctx : NearInterface.Context) (raw : Storage) (st : Option Storage) (rest : Nat)
    (hmethod : ctx.method = "save") (hprepare : PreparationLimits ctx.protocol)
    (hinput : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (inputFailureAttemptBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw rest)) :
    NearInterface.Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.execOn code raw ctx) (modelStep ctx st ()) := by
  rw [modelStep_input_too_long ctx st hinput]
  have hr := run_save_input_too_long_public ctx.protocol (Near.Boundary.toVMContext ctx) raw
    rest hprepare hinput hcredits
  have hf := inputFailureOutcome_fields ctx.protocol (Near.Boundary.toVMContext ctx) raw
  unfold Near.Boundary.execOn
  simp only [show code.code.decodeIssue = none by rfl]
  change NearInterface.Matches (model gasBound) ctx raw.toFinset
    (Near.Boundary.observe ctx raw
      (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _) _
  rw [hmethod, hr]
  apply Near.Boundary.observe_matches_abort
  exact ⟨.hostError (.guestPanic "input: register size exceeded"), hf.1, rfl, hf.2.1⟩

private theorem executionActive_extCosts (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (executionActive cfg ctx raw).extCosts = cfg.wasm.extCosts := by
  have hf := congrArg NearState.extCosts
    (MeteredHosts.applyCharges_frame (ctx.toNearState cfg raw) (loadingCharges 0) loading_burnsOnly)
  simpa only [executionActive, executionLoaded, chargeHost, VMContext.toNearState] using hf

theorem inputFailureAttemptBudget_eq (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (rest : Nat) : inputFailureAttemptBudget cfg ctx raw rest = inputFailureCost cfg + rest := by
  simp only [inputFailureAttemptBudget, inputFailureBudget, MeteredHosts.Input.cost,
    executionStore, initialized_host, executionActive_extCosts, VMContext.toNearState,
    loadingCharges, MeteredHosts.burnSum, MeteredHosts.burnCost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, inputFailureCost]
  omega

/-- The concrete failure bound directly supplies the boundary's initial gas
credits. Both prepaid and burn limits remain represented in `gasLimit`. -/
theorem execOn_matches_input_too_long_of_gasLimit
    (gasBound : NearInterface.Context → Option Storage → Unit → Nat)
    (ctx : NearInterface.Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hprepare : PreparationLimits ctx.protocol)
    (hinput : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length)
    (hgas : inputFailureCost ctx.protocol ≤ ctx.gasLimit) :
    NearInterface.Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.execOn code raw ctx) (modelStep ctx st ()) := by
  apply execOn_matches_input_too_long gasBound ctx raw st 0 hmethod hprepare hinput
  apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
  simpa only [inputFailureAttemptBudget_eq, Nat.add_zero] using hgas

/-- The early failure's burnt gas is bounded together with its functional
contract, including loading and activation, rather than by a measured run. -/
theorem inputFailureOutcome_burnt_le (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (rest : Nat) (hinput : cfg.wasm.limits.maxRegisterSize < ctx.input.length)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits (inputFailureAttemptBudget cfg ctx raw rest)) :
    (inputFailureOutcome cfg ctx raw).burntGas ≤ inputFailureCost cfg + rest := by
  let budget := inputFailureBudget cfg.wasm (executionStore cfg ctx raw) rest
  have hl := MeteredHosts.applyCharges_credits (ctx.toNearState cfg raw) (loadingCharges 0)
    (8 * cfg.wasm.regularOpCost + budget) loading_burnsOnly hcredits
  have hload : (executionLoaded cfg ctx raw).gas.burnt =
      MeteredHosts.burnSum cfg.wasm.extCosts (loadingCharges 0) := by
    simpa only [executionLoaded, VMContext.toNearState, Nat.zero_add] using hl.2.1
  have ha := GasCounter.burn_credits (executionLoaded cfg ctx raw).gas
    (8 * cfg.wasm.regularOpCost) budget (by simpa only [executionLoaded] using hl.2.2.2.2)
  have hactive : (executionActive cfg ctx raw).gas.burnt =
      (executionLoaded cfg ctx raw).gas.burnt + 8 * cfg.wasm.regularOpCost := by
    simpa only [executionActive, chargeHost] using ha.2.1
  have hi : (executionActive cfg ctx raw).gas.Credits budget := by
    simpa only [executionActive, chargeHost] using ha.2.2.2
  have hlimit : withinLimit (executionStore cfg ctx raw).host.config.maxRegisterLen
      (executionStore cfg ctx raw).host.context.input.length = false := by
    simp only [executionStore, initialized_host, executionActive_config, executionActive_input]
    simp [VMContext.toNearState, withinLimit, Nat.not_le_of_gt hinput]
  have hw := wp_save_input_too_long cfg (executionStore cfg ctx raw) execLimits rest
    (by rfl) (by rfl) hlimit hi
  obtain ⟨_, hp, _⟩ := hw.result
  have hb := hw.burnt_le
  rw [hp.2.1] at hb
  simp only [StepResult.host, atCode, executionStore, initialized_host] at hb
  have he := inputFailure_error cfg.wasm (executionStore cfg ctx raw)
    (executionActive_fresh cfg ctx raw).1 (executionActive_fresh cfg ctx raw).2.1
  have htotal := inputFailureAttemptBudget_eq cfg ctx raw rest
  change MeteredHosts.burnSum cfg.wasm.extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost + budget) = inputFailureCost cfg + rest at htotal
  simp only [inputFailureOutcome, outcomeOfExecution, StepResult.host, he]
  change (inputFailureStore cfg.wasm (executionStore cfg ctx raw)).host.gas.burnt ≤ _
  change (inputFailureStore cfg.wasm (executionStore cfg ctx raw)).host.gas.burnt ≤
    (executionActive cfg ctx raw).gas.burnt + budget at hb
  omega

/-- The receipt-level failure branch satisfies both model matching and its
symbolic used-gas bound, whenever the two actual gas limits cover that cost. -/
theorem execOn_input_failure_bounded
    (gasBound : NearInterface.Context → Option Storage → Unit → Nat)
    (ctx : NearInterface.Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hprepare : PreparationLimits ctx.protocol)
    (hinput : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length)
    (hgas : inputFailureCost ctx.protocol ≤ ctx.gasLimit) :
    NearInterface.Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.execOn code raw ctx) (modelStep ctx st ()) ∧
    (Near.Boundary.execOn code raw ctx).usedGas ≤ inputFailureCost ctx.protocol := by
  constructor
  · exact execOn_matches_input_too_long_of_gasLimit gasBound ctx raw st hmethod hprepare hinput hgas
  · have hc : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
        (inputFailureAttemptBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw 0) := by
      apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
      simpa only [inputFailureAttemptBudget_eq, Nat.add_zero] using hgas
    have hr := run_save_input_too_long_public ctx.protocol (Near.Boundary.toVMContext ctx) raw
      0 hprepare hinput hc
    have hb := inputFailureOutcome_burnt_le ctx.protocol (Near.Boundary.toVMContext ctx) raw 0 hinput hc
    have hf := inputFailureOutcome_fields ctx.protocol (Near.Boundary.toVMContext ctx) raw
    unfold Near.Boundary.execOn
    simp only [show code.code.decodeIssue = none by rfl]
    change (Near.Boundary.observe ctx raw
      (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas ≤ _
    rw [hmethod, hr]
    simpa only [Near.Boundary.observe, hf.1, Nat.add_zero] using hb

end WNear.Skeleton
