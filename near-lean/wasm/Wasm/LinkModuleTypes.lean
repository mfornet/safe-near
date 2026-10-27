import Wasm.Link

/-! Linking retains the actual module type vector in the final instance. -/
namespace Wasm.Link

theorem allocGlobals_types (s : Store H) (inst : ModuleInst) (globals : List Global)
    {after : Store H} {result : ModuleInst} (h : allocGlobals s inst globals = .ok (after, result)) :
    result.types = inst.types := by
  induction globals generalizing s inst with
  | nil =>
    simp only [allocGlobals, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ rfl
  | cons g gs ih =>
    simp only [allocGlobals] at h
    split at h
    · cases h
    · have ht := ih _ _ h
      exact ht

/-- Successful linking changes address spaces and exports, retaining types
through all global, element and data initialization stages. -/
theorem instantiateModule_types (store : Store H) (vm : ValidModule) (imports : List ExternVal)
    {after : Store H} {inst : ModuleInst}
    (h : instantiateModule store vm imports = .ok (after, inst)) :
    inst.types = vm.module.types := by
  unfold instantiateModule at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i pair globalsStore globalInst hglobals
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact allocGlobals_types _ _ _ hglobals

end Wasm.Link
