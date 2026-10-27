import Skeleton.Prepared
import Skeleton.Body

/-!
# From the actual VM entry point to the walking body

The loading charge, validation, linking and entry activation are distinct
from the method's fifteen opcodes. This file exposes those costs and connects
`runAttempt` to the actual initialized body, with memory kept symbolic.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- The exact configured memory installed by preparation. -/
def preparedData (cfg : RuntimeConfig) : Memory :=
  dataMemory cfg.wasm.limits.initialMemoryPages (some cfg.wasm.limits.maxMemoryPages)

/-- The first active frame produced by `Exec.startWasm`. -/
def entryConfig (cfg : RuntimeConfig) (host : NearState) : Config NearState :=
  atCode (initializedStore cfg host (preparedData cfg)) execLimits #[] saveFrame []
    module.funcs[0]!.body

theorem start_save (cfg : RuntimeConfig) (host : NearState) :
    Exec.startWasm (initializedStore cfg host (preparedData cfg)) execLimits
      moduleInstance.funcAddrs[4]! [] = some (entryConfig cfg host) := by
  rfl

/-- Input, storage, logging and returning a value are never gated imports. -/
theorem prepared_hosts_enabled (cfg : RuntimeConfig) :
    (prepareMemory cfg module).importDecls.any
      (fun decl => decl.module == "env" && disabledHost cfg decl.name) = false := by
  simp [prepareMemory, module, Module.importDecls, Module.importedFuncTypes, disabledHost]

/-- The real VM entry reduces to the initialized body after its loading
charge. No assumption mentions execution of the method itself. -/
theorem runAttempt_save (cfg : RuntimeConfig) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) (fuel : Nat) (loaded : NearState)
    (hpositive : 0 < cfg.wasm.limits.initialMemoryPages)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hload : applyCharges (ctx.toNearState cfg storage) (loadingCharges 0) = (loaded, none)) :
    runAttempt cfg module 0 "save" ctx storage fuel =
      let result := runInitialized cfg.wasm fuel (.next (entryConfig cfg loaded))
      outcomeOfExecution ctx storage result.1 result.2 := by
  simp only [runAttempt, show "save".isEmpty = false by decide, Bool.false_eq_true, ↓reduceIte,
    prepared_limits cfg.wasm.limits htypes hfunctions, hload,
    prepared_validate_eq cfg hminmax hmax, prepared_no_start, Option.isSome_none,
    prepared_hosts_enabled, prepared_save_export, prepared_save_type]
  simp only [show (({ params := [], results := [] } : FuncType).params.isEmpty &&
      ({ params := [], results := [] } : FuncType).results.isEmpty) = true by rfl,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, prepared_resolve_hosts,
    hosts_imports, instantiate_prepared cfg loaded hpositive hminmax hmax]
  have hs := start_save cfg loaded
  unfold preparedData at hs
  rw [hs]

/-- The zero-local entry activation costs eight regular operations. -/
theorem entryCost_save (cfg : RuntimeConfig) (host : NearState) :
    entryCost cfg.wasm (.next (entryConfig cfg host)) = 8 * cfg.wasm.regularOpCost := by
  simp [entryCost, entryConfig, atCode, Config.locals, saveFrame, activationGas]

/-- Sufficient activation credits expose the metered body with its residual
credits. The entry charge cannot touch memory or any functional host state. -/
theorem runInitialized_save (cfg : RuntimeConfig) (host : NearState) (fuel rest : Nat)
    (hcredits : host.gas.Credits (8 * cfg.wasm.regularOpCost + rest)) :
    runInitialized cfg.wasm fuel (.next (entryConfig cfg host)) =
      runMetered cfg.wasm fuel
        (.next (entryConfig cfg (chargeHost host (8 * cfg.wasm.regularOpCost)).1)) := by
  have hc := Pays.chargeWasm (.next (entryConfig cfg host))
    (8 * cfg.wasm.regularOpCost) rest hcredits
  simp only [runInitialized, entryCost_save]
  rw [show (chargeWasm (.next (entryConfig cfg host))
    (8 * cfg.wasm.regularOpCost)).2 = none from hc.1]
  rfl

/-- The loading plan for the syntax-level module contains only burns. -/
private theorem loading_burnsOnly :
    ∀ charge ∈ loadingCharges 0, MeteredHosts.BurnsOnly charge := by
  simp [loadingCharges, MeteredHosts.BurnsOnly]

/-- Sufficient loading credits discharge the startup charge premise. The
remaining credits are available for activation and the body. -/
theorem runAttempt_save_credits (cfg : RuntimeConfig) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) (fuel rest : Nat)
    (hpositive : 0 < cfg.wasm.limits.initialMemoryPages)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hcredits : (ctx.toNearState cfg storage).gas.Credits
      (MeteredHosts.burnSum (ctx.toNearState cfg storage).extCosts (loadingCharges 0) + rest)) :
    let loaded := (applyCharges (ctx.toNearState cfg storage) (loadingCharges 0)).1
    runAttempt cfg module 0 "save" ctx storage fuel =
      (let result := runInitialized cfg.wasm fuel (.next (entryConfig cfg loaded));
        outcomeOfExecution ctx storage result.1 result.2) ∧ loaded.gas.Credits rest := by
  have hc := MeteredHosts.applyCharges_credits (ctx.toNearState cfg storage) (loadingCharges 0)
    rest loading_burnsOnly hcredits
  exact ⟨runAttempt_save cfg ctx storage fuel _ hpositive hminmax hmax htypes hfunctions
    (Prod.ext rfl hc.1), hc.2.2.2.2⟩

end WNear.Skeleton
