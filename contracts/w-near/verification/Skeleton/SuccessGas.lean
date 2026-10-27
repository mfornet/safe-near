import Skeleton.SuccessExecution
import Skeleton.StorageCredits

/-!
# Symbolic used-gas bound for the successful walking body

The exact loading and activation charges precede the body's WP. The residual
credit frame is retained in the bound, rather than spent or measured afterward.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- The computed final machine spends at most the original total budget,
retaining the original residual credits. -/
theorem executionFinal_used_add_rest_le (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64)
    (hprepare : PreparationLimits cfg)
    (h : SaveResources cfg ctx raw storage storageCost rest written) :
    (executionFinal cfg ctx raw storage).host.gas.used + rest ≤
      executionBudget cfg ctx raw storage storageCost rest := by
  let body := successBudget cfg (executionStore cfg ctx raw) storage storageCost rest
  have hl := MeteredHosts.applyCharges_credits (ctx.toNearState cfg raw) (loadingCharges 0)
    (8 * cfg.wasm.regularOpCost + body) (by simp [loadingCharges, MeteredHosts.BurnsOnly]) h.credits
  have ha := GasCounter.burn_credits (executionLoaded cfg ctx raw).gas
    (8 * cfg.wasm.regularOpCost) body (by simpa only [executionLoaded] using hl.2.2.2.2)
  have hac : (executionActive cfg ctx raw).gas.Credits body := by
    simpa only [executionActive, chargeHost] using ha.2.2.2
  have hloadburn : (executionLoaded cfg ctx raw).gas.burnt =
      MeteredHosts.burnSum (ctx.toNearState cfg raw).extCosts (loadingCharges 0) := by
    simpa only [executionLoaded, VMContext.toNearState, Nat.zero_add] using hl.2.1
  have hloadprom : (executionLoaded cfg ctx raw).gas.promises = 0 := by
    simpa only [executionLoaded, VMContext.toNearState] using hl.2.2.1
  have hactive : (executionActive cfg ctx raw).gas.used =
      MeteredHosts.burnSum (ctx.toNearState cfg raw).extCosts (loadingCharges 0) +
        8 * cfg.wasm.regularOpCost := by
    simp only [executionActive, chargeHost, GasCounter.used, ha.2.1, ha.2.2.1, hloadburn, hloadprom, Nat.add_zero]
  have hw := wp_save_success cfg (executionActive cfg ctx raw) cfg.wasm.limits.initialMemoryPages
    (some cfg.wasm.limits.maxMemoryPages) storage storageCost rest written execLimits hprepare.positive
    (by rw [executionActive_config, executionActive_input]; exact h.inputLimit)
    h.memory (by rw [executionActive_input]; exact h.register)
    (by rw [executionActive_input]; exact h.returnLimit) h.logCount h.logSpace h.readCost h.logPush hac h.storageCall
  obtain ⟨remaining, hp, _, _, hu, _⟩ := hw.result
  rw [hp.2.1, hp.1] at hu
  have hu' : (executionFinal cfg ctx raw storage).host.gas.used + rest ≤
      (executionActive cfg ctx raw).gas.used + body := by
    simpa only [executionFinal, executionStore, preparedData, StepResult.host, atCode, initialized_host, body] using hu
  rw [hactive] at hu'
  simpa only [executionBudget, body, Nat.add_assoc] using hu'

/-- Empty promise conversion distributes no gas, so the normal outcome exposes
exactly the final machine's used gas. -/
theorem executionOutcome_used (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (hpromises : storage.host.promises = []) :
    (outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw storage)) none).usedGas =
      (executionFinal cfg ctx raw storage).host.gas.used := by
  have hp := (executionFinal_promises cfg ctx raw storage).trans hpromises
  simp only [outcomeOfExecution, StepResult.host, hp, convertPromises, convertPromisesFrom,
    PromiseGraph.returnData?, executionFinal_returnedPromise, executionFinal_returnData,
    distributeGas_no_handles, Nat.add_zero]

/-- The actual public VM runner obeys the symbolic total bound. This includes
loading and entry activation, not only the fifteen body opcodes. -/
theorem run_save_success_used_add_rest_le (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64)
    (hprepare : PreparationLimits cfg)
    (h : SaveResources cfg ctx raw storage storageCost rest written)
    (hpromises : storage.host.promises = []) :
    (run cfg module 0 "save" ctx raw).usedGas + rest ≤
      executionBudget cfg ctx raw storage storageCost rest := by
  rw [run_save_success_public cfg ctx raw storage storageCost rest written hprepare h hpromises,
    executionOutcome_used cfg ctx raw storage hpromises]
  exact executionFinal_used_add_rest_le cfg ctx raw storage storageCost rest written hprepare h

private theorem executionOutcome_gas_fields (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (storage : HostStore NearState) (hpromises : storage.host.promises = []) :
    let o := outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw storage)) none
    o.aborted = none ∧ o.receipts = [] ∧
    o.burntGas = (executionFinal cfg ctx raw storage).host.gas.burnt ∧ o.distributedGas = 0 := by
  have hp := (executionFinal_promises cfg ctx raw storage).trans hpromises
  simp only [outcomeOfExecution, StepResult.host, hp, convertPromises, convertPromisesFrom,
    PromiseGraph.returnData?, executionFinal_returnedPromise, executionFinal_returnData,
    distributeGas_no_handles, and_self]

/-- Every boundary exit exposes at most the VM's used gas when burnt gas
is bounded by used gas. This also covers action, receipt and stake failures. -/
theorem observe_used_le (ctx : NearInterface.Context) (raw : Storage) (o : VMOutcome)
    (issue : Option ExecutionIssue) (receiptError : Option Near.RuntimeError)
    (hburn : o.burntGas ≤ o.usedGas) :
    (Near.Boundary.observe ctx raw o issue receiptError).usedGas ≤ o.usedGas := by
  unfold Near.Boundary.observe
  repeat' split
  all_goals dsimp only
  all_goals try split
  all_goals first | exact hburn | exact Nat.sub_le _ _

/-- The public receipt observation retains the bound, including on a later
storage-stake rejection. Such rejection exposes burnt gas, bounded by used gas. -/
theorem execOn_save_success_used_add_rest_le (ctx : NearInterface.Context) (raw : Storage)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64)
    (hmethod : ctx.method = "save") (hprepare : PreparationLimits ctx.protocol)
    (h : SaveResources ctx.protocol (Near.Boundary.toVMContext ctx) raw storage storageCost rest written)
    (hpromises : storage.host.promises = []) :
    (Near.Boundary.execOn code raw ctx).usedGas + rest ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw storage storageCost rest := by
  let o := outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
    (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw storage)) none
  have hr := run_save_success_public ctx.protocol (Near.Boundary.toVMContext ctx) raw storage
    storageCost rest written hprepare h hpromises
  have hu := run_save_success_used_add_rest_le ctx.protocol (Near.Boundary.toVMContext ctx) raw storage
    storageCost rest written hprepare h hpromises
  rw [hr] at hu
  have hf := executionOutcome_gas_fields ctx.protocol (Near.Boundary.toVMContext ctx) raw storage hpromises
  change o.aborted = none ∧ o.receipts = [] ∧
    o.burntGas = _ ∧ o.distributedGas = 0 at hf
  have hbu : o.burntGas ≤ o.usedGas := by
    rw [hf.2.2.1, executionOutcome_used ctx.protocol (Near.Boundary.toVMContext ctx) raw storage hpromises]
    exact Nat.le_add_right _ _
  unfold Near.Boundary.execOn
  simp only [code]
  change (Near.Boundary.observe ctx raw
    (run ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw) _ _).usedGas + rest ≤ _
  rw [hmethod, hr]
  exact Nat.le_trans (Nat.add_le_add_right (observe_used_le ctx raw o _ _ hbu) rest) hu

end WNear.Skeleton
