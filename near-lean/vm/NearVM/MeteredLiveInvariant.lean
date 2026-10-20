import NearVM.Run
import NearVM.LiveInvariant

namespace Wasm.Near

theorem chargeWasm_liveInvariant {P : NearState → Prop}
    (hcharge : ∀ (config : SmallStep.Config NearState) (cost : Nat), P config.store.wasm.host → P (chargeWasm config cost).1.store.wasm.host)
    (config : SmallStep.Config NearState) (cost : Nat) (h : ConfigLiveInvariant P config) :
    ConfigLiveInvariant P (chargeWasm config cost).1 :=
by
  refine ⟨h.1, ?_⟩
  have hl := h.2
  cases he : config.expr <;>
    simp only [SmallStep.Config.LiveHost, chargeWasm, he] at hl ⊢
  · exact hcharge config cost hl
  · exact hcharge config cost hl

theorem runMetered_liveInvariant (P : NearState → Prop)
    (hcharge : ∀ (config : SmallStep.Config NearState) (cost : Nat), P config.store.wasm.host → P (chargeWasm config cost).1.store.wasm.host)
    (cfg : WasmConfig) (fuel : Nat)
    (config : SmallStep.Config NearState) (h : ConfigLiveInvariant P config) :
    ConfigLiveInvariant P (runMetered cfg fuel config).1 := by
  induction fuel generalizing config with
  | zero => cases he : config.expr <;> simpa only [runMetered, he] using h
  | succ fuel ih =>
    cases he : config.expr with
    | done values => simpa only [runMetered, he] using h
    | trapped reason => simpa only [runMetered, he] using h
    | running thread =>
      cases hc : chargeWasm config (nextInstructionGas cfg config) with
      | mk paid error =>
        have hp := chargeWasm_liveInvariant hcharge config (nextInstructionGas cfg config) h
        rw [hc] at hp
        cases error with
        | some error => simpa only [runMetered, he, hc] using hp
        | none =>
          cases hs : SmallStep.stepChecked? paid with
          | error error => simpa only [runMetered, he, hc, hs] using hp
          | ok transition =>
            cases transition with
            | none => simpa only [runMetered, he, hc, hs] using hp
            | some transition =>
              obtain ⟨kind, next⟩ := transition
              have hn := step_preserves_liveInvariant (SmallStep.stepChecked?_sound hs) hp
              cases hf : chargeWasm next (frameTransitionGas cfg paid next) with
              | mk final error =>
                have hfinal := chargeWasm_liveInvariant hcharge next (frameTransitionGas cfg paid next) hn
                rw [hf] at hfinal
                cases error with
                | some error => simpa only [runMetered, he, hc, hs, hf] using hfinal
                | none => simpa only [runMetered, he, hc, hs, hf] using ih final hfinal

end Wasm.Near
