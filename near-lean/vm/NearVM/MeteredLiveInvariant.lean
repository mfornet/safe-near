import NearVM.Run
import NearVM.LiveInvariant

namespace Wasm.Near

theorem chargeConfig_liveInvariant {P : NearState → Prop}
    (hcharge : ∀ (ns : NearState) (cost : Nat), P ns → P (chargeHost ns cost).1)
    (c : Config NearState) (cost : Nat) (h : ConfigLiveInvariant P c) :
    ConfigLiveInvariant P (chargeConfig c cost).1 :=
  ⟨h.1, hcharge c.store.host cost h.2⟩

theorem chargeWasm_liveInvariant {P : NearState → Prop}
    (hcharge : ∀ (ns : NearState) (cost : Nat), P ns → P (chargeHost ns cost).1)
    (m : Machine) (cost : Nat) (h : MachineLiveInvariant P m) :
    MachineLiveInvariant P (chargeWasm m cost).1 := by
  cases m with
  | next c => exact chargeConfig_liveInvariant hcharge c cost h
  | done values store => exact ⟨h.1, hcharge store.host cost h.2⟩
  | trap reason store => exact h

theorem runMetered_liveInvariant (P : NearState → Prop)
    (hcharge : ∀ (ns : NearState) (cost : Nat), P ns → P (chargeHost ns cost).1)
    (cfg : WasmConfig) (fuel : Nat) (m : Machine) (h : MachineLiveInvariant P m) :
    MachineLiveInvariant P (runMetered cfg fuel m).1 := by
  induction fuel generalizing m with
  | zero => cases m <;> simpa only [runMetered] using h
  | succ fuel ih =>
    cases m with
    | done values store => simpa only [runMetered] using h
    | trap reason store => simpa only [runMetered] using h
    | next c =>
      have hp := chargeConfig_liveInvariant hcharge c (nextInstructionGas cfg c) h
      simp only [runMetered]
      split
      · exact hp
      · have hn := step_liveInvariant hp
        have hfinal := chargeWasm_liveInvariant hcharge
          (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
          (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
            (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)) hn
        split
        · exact hfinal
        · exact ih _ hfinal

end Wasm.Near
