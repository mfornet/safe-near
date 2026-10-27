import Binary.Module
import NearVM.Run
import NearVM.MeteredResolutionLookup

/-! Small import-layout facts, independent of deployed data initialization. -/
namespace WNear.Binary.ImportLayout
open Wasm Wasm.Near
set_option maxRecDepth 10000

theorem declarations_length : wNearModule.importDecls.length = 48 := by kernel_rfl

theorem imported_functions_length : wNearModule.importedFuncTypes.length = 48 := by kernel_rfl

theorem imports_size : wNearModule.imports.size = 48 := by kernel_rfl

theorem prepared_declarations_length (cfg : RuntimeConfig) :
    (prepareMemory cfg wNearModule).importDecls.length = 48 :=
  declarations_length

theorem prepared_no_start (cfg : RuntimeConfig) :
    (prepareMemory cfg wNearModule).start = none := rfl

/-- Successful validation retains precisely the prepared syntax object; no
evaluation of the deployed validator or data bytes is assumed here. -/
theorem validated_module (cfg : RuntimeConfig) (features : Features) (vm : ValidModule)
    (h : (prepareMemory cfg wNearModule).validate features = .ok vm) :
    vm.module = prepareMemory cfg wNearModule := by
  unfold Module.validate at h
  cases hc : Validate.module features (prepareMemory cfg wNearModule) with
  | error e => simp [hc] at h
  | ok u =>
    cases u
    simp [hc] at h
    cases h
    rfl

/-- Every deployed function import is present in the actual metered host
registry. Configuration-dependent implementations do not change resolution. -/
theorem resolves (cfg : RuntimeConfig) :
    (resolveMetered cfg (prepareMemory cfg wNearModule)).isOk = true := by
  rfl

noncomputable def hosts (cfg : RuntimeConfig) : HostEnv NearState :=
  match h : resolveMetered cfg (prepareMemory cfg wNearModule) with
  | .ok env => env
  | .error _ => False.elim (by
      have hs := resolves cfg
      simp [h, Except.isOk, Except.toBool] at hs)

theorem resolve_hosts (cfg : RuntimeConfig) :
    resolveMetered cfg (prepareMemory cfg wNearModule) = .ok (hosts cfg) := by
  unfold hosts
  split
  · next env h => exact h
  · next e h => have hs := resolves cfg; simp [h, Except.isOk, Except.toBool] at hs

theorem hosts_length (cfg : RuntimeConfig) : (hosts cfg).funcs.length = 48 := by
  have h := resolveMetered_length cfg (prepareMemory cfg wNearModule) (hosts cfg) (resolve_hosts cfg)
  simpa only [prepared_declarations_length] using h

end WNear.Binary.ImportLayout
