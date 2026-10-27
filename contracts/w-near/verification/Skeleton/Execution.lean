import Skeleton.Startup
import Skeleton.Success

/-!
# Whole VM-attempt execution from local host contracts

Loading, entry activation and the active body's credits remain separate. The
remaining semantic frontier is the single storage host call, not execution of
the method or a suffix. The prepared memory remains symbolic throughout.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

@[irreducible] def executionLoaded (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) : NearState :=
  (applyCharges (ctx.toNearState cfg raw) (loadingCharges 0)).1

@[irreducible] def executionActive (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) : NearState :=
  (chargeHost (executionLoaded cfg ctx raw) (8 * cfg.wasm.regularOpCost)).1

def executionStore (cfg : RuntimeConfig) (ctx : VMContext) (raw : List (List UInt8 × List UInt8)) :=
  initializedStore cfg (executionActive cfg ctx raw) (preparedData cfg)

@[irreducible] def executionFinal (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState) : Store NearState :=
  (successResults cfg (executionStore cfg ctx raw) postStorage).finalStore cfg.wasm
    (executionStore cfg ctx raw)

/-- The complete budget: loading, eight entry opcodes, then the fifteen-opcode
body and its four host costs. `rest` is retained at the final store. -/
def executionBudget (cfg : RuntimeConfig) (ctx : VMContext) (raw : List (List UInt8 × List UInt8))
    (postStorage : HostStore NearState) (storageCost rest : Nat) : Nat :=
  MeteredHosts.burnSum (ctx.toNearState cfg raw).extCosts (loadingCharges 0) +
    (8 * cfg.wasm.regularOpCost +
      successBudget cfg (executionStore cfg ctx raw) postStorage storageCost rest)

/-- Combining startup and the body gives twenty-three regular operations;
the four host charge plans and retained credits are additional. -/
theorem executionBudget_eq (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState)
    (storageCost rest : Nat) :
    executionBudget cfg ctx raw postStorage storageCost rest =
      MeteredHosts.burnSum (ctx.toNearState cfg raw).extCosts (loadingCharges 0) +
      23 * cfg.wasm.regularOpCost +
      MeteredHosts.Input.cost (successInputBefore cfg (executionStore cfg ctx raw)).host +
      storageCost + MeteredHosts.burnSum
        (successLogBefore cfg (executionStore cfg ctx raw) postStorage).host.extCosts savedCharges +
      returnCost cfg.wasm (successReturnBefore cfg (executionStore cfg ctx raw) postStorage) + rest := by
  unfold executionBudget successBudget
  omega

private theorem loading_burnsOnly :
    ∀ charge ∈ loadingCharges 0, MeteredHosts.BurnsOnly charge := by
  simp [loadingCharges, MeteredHosts.BurnsOnly]

theorem executionActive_config (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) :
    (executionActive cfg ctx raw).config = (ctx.toNearState cfg raw).config := by
  have hf := congrArg NearState.config
    (MeteredHosts.applyCharges_frame (ctx.toNearState cfg raw) (loadingCharges 0) loading_burnsOnly)
  simpa only [executionActive, executionLoaded, chargeHost] using hf

theorem executionActive_input (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) :
    (executionActive cfg ctx raw).context.input = ctx.input := by
  have hf := congrArg (fun host : NearState => host.context.input)
    (MeteredHosts.applyCharges_frame (ctx.toNearState cfg raw) (loadingCharges 0) loading_burnsOnly)
  change (applyCharges (ctx.toNearState cfg raw) (loadingCharges 0)).1.context.input = ctx.input at hf
  simpa only [executionActive, executionLoaded, chargeHost] using hf

private theorem chargedMany_promises (store : Store NearState) (cost n : Nat) :
    (chargedMany store cost n).host.promises = store.host.promises := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => simpa only [chargedMany, chargedStore, chargeHost] using ih (chargedStore store cost)

private theorem savedAfter_promises (st : HostStore NearState) :
    (savedAfter st).host.promises = st.host.promises := by
  have hf := congrArg NearState.promises
    (MeteredHosts.applyCharges_frame st.host savedCharges (by
      simp only [savedCharges, extCharges, List.mem_map]
      rintro _ ⟨_, _, rfl⟩
      trivial))
  simpa only [savedAfter, MeteredHosts.Output.paidStore] using hf

private theorem returnedAfter_promises (cfg : WasmConfig) (store : Store NearState) (bytes : List UInt8) :
    (returnedAfter cfg store bytes).host.promises = store.host.promises := by
  have hf := congrArg NearState.promises
    (MeteredHosts.applyCharges_frame (inputBefore cfg store moduleInstance).host
      (returnCharges cfg store)
      (MeteredHosts.Output.valueReturn_burnsOnly (inputBefore cfg store moduleInstance) u64Max 0))
  simpa only [returnedAfter, MeteredHosts.Output.paidStore, inputBefore, chargedStore, chargeHost] using hf

private theorem successReturn_promises (cfg : RuntimeConfig) (store : Store NearState)
    (postStorage : HostStore NearState) :
    (successReturnBefore cfg store postStorage).host.promises = postStorage.host.promises := by
  simp only [successReturnBefore, chargedMany_promises, commitCall_host, successLogAfter,
    savedAfter_promises, inputBefore, chargedStore, chargeHost, successLogBefore]

/-- Output host contracts frame storage's promise graph. -/
theorem executionFinal_promises (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState) :
    (executionFinal cfg ctx raw postStorage).host.promises = postStorage.host.promises := by
  simp only [executionFinal, HostResults.finalStore, commitCall_host,
    successResults_returned, successResults_beforeReturn, returnedAfter_promises, successReturn_promises]

/-- Returning bytes clears any previous promise-return selector. -/
theorem executionFinal_returnedPromise (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState) :
    (executionFinal cfg ctx raw postStorage).host.returnedPromise = none := by
  simp only [executionFinal, HostResults.finalStore, commitCall_host,
    successResults_returned, successResults_beforeReturn]
  rfl

/-- A local empty-promise postcondition suffices to exclude conversion failure
when the normally terminated machine is projected to its VM outcome. -/
theorem executionOutcome_succeeds (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState)
    (hpromises : postStorage.host.promises = []) :
    (outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw postStorage)) none).aborted = none := by
  have hp := (executionFinal_promises cfg ctx raw postStorage).trans hpromises
  simp only [outcomeOfExecution, StepResult.host, hp, convertPromises, convertPromisesFrom,
    PromiseGraph.returnData?, executionFinal_returnedPromise]

/-- Whole `runAttempt`: no startup or method execution equation is assumed.
All host/resource premises are local to the original or post-storage state. -/
theorem runAttempt_save_success (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (fuel : Nat)
    (hpositive : 0 < cfg.wasm.limits.initialMemoryPages)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hfuel : 16 ≤ fuel)
    (hinputLimit : withinLimit (ctx.toNearState cfg raw).config.maxRegisterLen ctx.input.length = true)
    (hmemory : postStorage.mem = preparedData cfg)
    (hregister : postStorage.host.registers 0 = some ctx.input)
    (hreturnLimit : withinLimit postStorage.host.config.maxReturnLen ctx.input.length = true)
    (hcount : logCountError postStorage = none)
    (hspace : 5 ≤ logSpace postStorage)
    (hreadCost : postStorage.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, postStorage.host.config.maxLogLen = some limit →
      totalLogLength postStorage + 5 ≤ limit)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits
      (executionBudget cfg ctx raw postStorage storageCost rest))
    (hstorage : StorageFrontier cfg (executionStore cfg ctx raw)
      postStorage storageCost rest written) :
    runAttempt cfg module 0 "save" ctx raw fuel =
      outcomeOfExecution ctx raw (.done [] (executionFinal cfg ctx raw postStorage)) none := by
  let budget := successBudget cfg (executionStore cfg ctx raw) postStorage storageCost rest
  have hs : runAttempt cfg module 0 "save" ctx raw fuel =
      (let result := runInitialized cfg.wasm fuel (.next (entryConfig cfg (executionLoaded cfg ctx raw)))
       outcomeOfExecution ctx raw result.1 result.2) ∧
      (executionLoaded cfg ctx raw).gas.Credits (8 * cfg.wasm.regularOpCost + budget) := by
    simpa only [executionLoaded] using runAttempt_save_credits cfg ctx raw fuel
      (8 * cfg.wasm.regularOpCost + budget) hpositive hminmax hmax htypes hfunctions hcredits
  have ha : (executionActive cfg ctx raw).gas.Credits budget := by
    have hc := GasCounter.burn_credits (executionLoaded cfg ctx raw).gas
      (8 * cfg.wasm.regularOpCost) budget hs.2
    simpa only [executionActive, chargeHost] using hc.2.2.2
  have hw := wp_save_success cfg (executionActive cfg ctx raw) cfg.wasm.limits.initialMemoryPages
    (some cfg.wasm.limits.maxMemoryPages) postStorage storageCost rest written execLimits hpositive
    (by rw [executionActive_config, executionActive_input]; exact hinputLimit) hmemory
    (by rw [executionActive_input]; exact hregister)
    (by rw [executionActive_input]; exact hreturnLimit) hcount hspace hreadCost hpush ha hstorage
  obtain ⟨remaining, hpost, _⟩ := hw.result
  have hrun16 : runMetered cfg.wasm 16 (.next (entryConfig cfg (executionActive cfg ctx raw))) =
      (.done [] (executionFinal cfg ctx raw postStorage), none) := by
    apply Prod.ext
    · simpa only [executionFinal, executionStore, entryConfig, preparedData] using hpost.2.1
    · exact hpost.2.2
  have hextra := runMetered_extra_fuel cfg.wasm 16
    (.next (entryConfig cfg (executionActive cfg ctx raw)))
    (by rw [hrun16]; simp) (fuel - 16)
  have hrun : runMetered cfg.wasm fuel (.next (entryConfig cfg (executionActive cfg ctx raw))) =
      (.done [] (executionFinal cfg ctx raw postStorage), none) := by
    rw [show 16 + (fuel - 16) = fuel by omega] at hextra
    exact hextra.trans hrun16
  rw [hs.1, runInitialized_save cfg (executionLoaded cfg ctx raw) fuel budget hs.2]
  unfold executionActive at hrun
  rw [hrun]

/-- With the local empty-promise invariant, the actual VM outcome succeeds. -/
theorem runAttempt_save_succeeds (cfg : RuntimeConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (postStorage : HostStore NearState)
    (storageCost rest : Nat) (written : UInt64) (fuel : Nat)
    (hpositive : 0 < cfg.wasm.limits.initialMemoryPages)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hfuel : 16 ≤ fuel)
    (hinputLimit : withinLimit (ctx.toNearState cfg raw).config.maxRegisterLen ctx.input.length = true)
    (hmemory : postStorage.mem = preparedData cfg)
    (hregister : postStorage.host.registers 0 = some ctx.input)
    (hreturnLimit : withinLimit postStorage.host.config.maxReturnLen ctx.input.length = true)
    (hcount : logCountError postStorage = none)
    (hspace : 5 ≤ logSpace postStorage)
    (hreadCost : postStorage.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, postStorage.host.config.maxLogLen = some limit →
      totalLogLength postStorage + 5 ≤ limit)
    (hcredits : (ctx.toNearState cfg raw).gas.Credits
      (executionBudget cfg ctx raw postStorage storageCost rest))
    (hstorage : StorageFrontier cfg (executionStore cfg ctx raw)
      postStorage storageCost rest written)
    (hpromises : postStorage.host.promises = []) :
    (runAttempt cfg module 0 "save" ctx raw fuel).aborted = none := by
  rw [runAttempt_save_success cfg ctx raw postStorage storageCost rest written fuel
    hpositive hminmax hmax htypes hfunctions hfuel hinputLimit hmemory hregister hreturnLimit
    hcount hspace hreadCost hpush hcredits hstorage]
  exact executionOutcome_succeeds cfg ctx raw postStorage hpromises

end WNear.Skeleton
