import Binary.Module
import NearVM.Run
import Wasm.ValidateModuleMemoryInvariant

/-! Configurable memory preparation preserves actual validator results.
The deployed memory declaration is checked here; the original complete-module
validation certificate remains an explicit premise of success corollaries. -/
namespace WNear.Binary
open Wasm Wasm.Near

theorem original_memory_types_ok : ∀ mem ∈ wNearModule.mems,
    Validate.memTypeOk mem.type = .ok () := by
  intro mem hm
  simp only [wNearModule, mems, Array.mem_singleton] at hm
  subst mem
  kernel_rfl

theorem prepared_validation_eq (cfg : RuntimeConfig) (features : Features)
    (horder : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    Validate.module features (prepareMemory cfg wNearModule) = Validate.module features wNearModule :=
  Validate.module_replace_limits features wNearModule
    cfg.wasm.limits.initialMemoryPages cfg.wasm.limits.maxMemoryPages
    original_memory_types_ok horder hmax

theorem prepared_validation_success (cfg : RuntimeConfig) (features : Features)
    (horder : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (hvalid : Validate.module features wNearModule = .ok ()) :
    Validate.module features (prepareMemory cfg wNearModule) = .ok () := by
  rw [prepared_validation_eq cfg features horder hmax, hvalid]

theorem prepared_validate_isOk (cfg : RuntimeConfig) (features : Features)
    (horder : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536) :
    ((prepareMemory cfg wNearModule).validate features).isOk = (wNearModule.validate features).isOk := by
  unfold Module.validate
  rw [prepared_validation_eq cfg features horder hmax]
  cases Validate.module features wNearModule <;> rfl

theorem prepared_validated_exists (cfg : RuntimeConfig) (features : Features)
    (horder : cfg.wasm.limits.initialMemoryPages ≤ cfg.wasm.limits.maxMemoryPages)
    (hmax : cfg.wasm.limits.maxMemoryPages ≤ 65536)
    (hvalid : Validate.module features wNearModule = .ok ()) :
    ∃ vm, (prepareMemory cfg wNearModule).validate features = .ok vm ∧
      vm.module = prepareMemory cfg wNearModule := by
  unfold Module.validate
  rw [prepared_validation_success cfg features horder hmax hvalid]
  exact ⟨_, rfl, rfl⟩

end WNear.Binary
