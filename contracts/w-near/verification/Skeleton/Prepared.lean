import Skeleton.Instantiation

/-!
# The walking module after NEAR memory preparation

Preparation substitutes the protocol's memory limits. The syntax and memory
values remain symbolic; proofs never materialize a configured memory page.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Configured memory bounds accepted by the Wasm validator. -/
theorem prepared_memTypeOk (cfg : RuntimeConfig)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    Validate.memTypeOk { limits := {
      min := cfg.wasm.limits.initialMemoryPages,
      max := some cfg.wasm.limits.maxMemoryPages } } = .ok () := by
  simp [Validate.memTypeOk, Validate.limitsOk, Nat.not_lt.mpr hminmax,
    Nat.not_lt.mpr hmax, Nat.not_lt.mpr (hminmax.trans hmax)]
  rfl

/-- The prepared module's only variable validation check is its memory type. -/
theorem prepared_validation_check (cfg : RuntimeConfig) :
    Validate.module (Features.nearcore true) (prepareMemory cfg module) = (do
      Validate.memTypeOk { limits := {
        min := cfg.wasm.limits.initialMemoryPages,
        max := some cfg.wasm.limits.maxMemoryPages } }
      pure ()) := by
  cases hc : Validate.memTypeOk { limits := {
        min := cfg.wasm.limits.initialMemoryPages,
        max := some cfg.wasm.limits.maxMemoryPages } } with
  | error e => simp [Validate.module, prepareMemory, module, hc]; rfl
  | ok u => cases u; simp [Validate.module, prepareMemory, module, hc]; rfl

/-- Preparation preserves validity when its memory limits fit Wasm32. -/
theorem prepared_validates (cfg : RuntimeConfig)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    ((prepareMemory cfg module).validate (Features.nearcore true)).isOk = true := by
  unfold Module.validate
  rw [prepared_validation_check, prepared_memTypeOk cfg hminmax hmax]
  rfl

/-- Validation result for the actual prepared module. -/
def preparedValidated (cfg : RuntimeConfig)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) : ValidModule :=
  match h : (prepareMemory cfg module).validate (Features.nearcore true) with
  | .ok v => v
  | .error _ => False.elim (by
      have hv := prepared_validates cfg hminmax hmax
      simp [h, Except.isOk, Except.toBool] at hv)

@[simp] theorem preparedValidated_module (cfg : RuntimeConfig)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    (preparedValidated cfg hminmax hmax).module = prepareMemory cfg module := by
  have checked (v : ValidModule)
      (h : (prepareMemory cfg module).validate (Features.nearcore true) = .ok v) :
      v.module = prepareMemory cfg module := by
    unfold Module.validate at h
    rw [prepared_validation_check, prepared_memTypeOk cfg hminmax hmax] at h
    cases h
    rfl
  unfold preparedValidated
  split
  · next v h => exact checked v h
  · next e h =>
      have hv := prepared_validates cfg hminmax hmax
      simp [h, Except.isOk, Except.toBool] at hv

theorem prepared_validate_eq (cfg : RuntimeConfig)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    (prepareMemory cfg module).validate (Features.nearcore true) =
      .ok (preparedValidated cfg hminmax hmax) := by
  unfold preparedValidated
  split
  · next v h => exact h
  · next e h =>
      have hv := prepared_validates cfg hminmax hmax
      simp [h, Except.isOk, Except.toBool] at hv

/-- Memory preparation has no effect on host resolution. -/
theorem prepared_resolve_hosts (cfg : RuntimeConfig) :
    resolveMetered cfg (prepareMemory cfg module) = .ok (hosts cfg) := rfl

theorem prepared_hosts_checkImports (cfg : RuntimeConfig) (host : NearState) :
    Link.checkImports ((hosts cfg).allocate (Store.empty host)).1 (prepareMemory cfg module)
      ((prepareMemory cfg module).imports.toList.zip [.func 0, .func 1, .func 2, .func 3]) =
      .ok () := rfl

/-- Instantiation of the actual prepared syntax, with its data write isolated. -/
theorem instantiate_prepared_module (cfg : RuntimeConfig) (host : NearState)
    (vm : ValidModule) (hvm : vm.module = prepareMemory cfg module) (memory : Memory)
    (hwrite : (Memory.new cfg.wasm.limits.initialMemoryPages
      (some cfg.wasm.limits.maxMemoryPages)).writeBytes 0 module.datas[0]!.init = some memory) :
    Link.instantiateModule ((hosts cfg).allocate (Store.empty host)).1 vm
      [.func 0, .func 1, .func 2, .func 3] = .ok (initializedStore cfg host memory, moduleInstance) := by
  change (Memory.new cfg.wasm.limits.initialMemoryPages (some cfg.wasm.limits.maxMemoryPages)).writeBytes
    0 ⟨#[107, 115, 97, 118, 101, 100]⟩ = some memory at hwrite
  simp only [Link.instantiateModule, hvm, prepared_hosts_checkImports]
  simp [prepareMemory, module, hosts, HostEnv.allocate, Store.empty, Store.allocFunc,
    NearHostFn.toHostFn, Link.importAddrs, Store.allocModule, Link.allocFuncs, Link.allocTables,
    Link.allocMems, Store.allocMem, Link.allocGlobals, Link.allocElems, Link.allocDatas,
    Store.allocData, Link.exportsOf, Store.setModule, Link.initElems, Link.initDatas,
    Link.indexed, Link.initData, Link.evalConst, Exec.i32, Store.memOf, Store.setMemOf,
    initializedStore, moduleInstance, hwrite]

/-- The actual prepared module initializes for every host state and legal,
positive configured memory size. The resulting pages remain symbolic. -/
theorem instantiate_prepared (cfg : RuntimeConfig) (host : NearState)
    (hpositive : 0 < cfg.wasm.limits.initialMemoryPages)
    (hminmax : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    Link.instantiateModule ((hosts cfg).allocate (Store.empty host)).1
      (preparedValidated cfg hminmax hmax) [.func 0, .func 1, .func 2, .func 3] =
      .ok (initializedStore cfg host (dataMemory cfg.wasm.limits.initialMemoryPages
        (some cfg.wasm.limits.maxMemoryPages)), moduleInstance) :=
  instantiate_prepared_module cfg host _ (preparedValidated_module cfg hminmax hmax) _
    (dataMemory_write _ _ hpositive)

/-- The walking module meets section-size preparation limits whenever the
optional type and function ceilings admit its four types and five functions.
All its other counted sections, bodies and local declarations have size zero. -/
theorem prepared_limits (limits : LimitConfig)
    (htypes : ∀ n, limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, limits.maxFunctionsNumberPerContract = some n → 5 ≤ n) :
    prepareLimitError limits module = none := by
  have typeWithin : limits.maxTypesPerContract.all (fun bound => decide (4 ≤ bound)) = true := by
    cases h : limits.maxTypesPerContract with
    | none => rfl
    | some n => simp only [Option.all]; exact decide_eq_true (htypes n h)
  have functionWithin (n : Nat) (hn : n ≤ 5) :
      limits.maxFunctionsNumberPerContract.all (fun bound => decide (n ≤ bound)) = true := by
    cases h : limits.maxFunctionsNumberPerContract with
    | none => rfl
    | some bound => simp only [Option.all]; exact decide_eq_true (hn.trans (hfunctions bound h))
  simp [prepareLimitError, module, typeWithin, functionWithin 1 (by decide),
    functionWithin 2 (by decide), functionWithin 3 (by decide), functionWithin 4 (by decide),
    functionWithin 5 (by decide)]

/-- Preparation changes no section counted by the preparation limits. -/
theorem prepared_limits_eq (cfg : RuntimeConfig) (limits : LimitConfig) :
    prepareLimitError limits (prepareMemory cfg module) = prepareLimitError limits module := rfl

@[simp] theorem prepared_no_start (cfg : RuntimeConfig) :
    (prepareMemory cfg module).start = none := rfl

@[simp] theorem prepared_save_export (cfg : RuntimeConfig) :
    (prepareMemory cfg module).exportFunc? "save" = some 4 := by
  change module.exportFunc? "save" = some 4
  exact save_export

@[simp] theorem prepared_save_type (cfg : RuntimeConfig) :
    (prepareMemory cfg module).funcType? 4 = some { params := [], results := [] } := by
  change module.funcType? 4 = some { params := [], results := [] }
  exact save_type

end WNear.Skeleton
