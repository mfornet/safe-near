import NearVM.Run
import NearVM.InterpreterInvariant

namespace Wasm.Near

theorem chargeConfig_hostInvariant {P : NearState → Prop}
    (hcharge : ∀ (ns : NearState) (cost : Nat), P ns → P (chargeHost ns cost).1)
    (c : Config NearState) (cost : Nat) (h : ConfigHostInvariant P c) :
    ConfigHostInvariant P (chargeConfig c cost).1 :=
  ⟨h.1, hcharge c.store.host cost h.2⟩

theorem chargeWasm_hostInvariant {P : NearState → Prop}
    (hcharge : ∀ (ns : NearState) (cost : Nat), P ns → P (chargeHost ns cost).1)
    (m : Machine) (cost : Nat) (h : MachineHostInvariant P m) :
    MachineHostInvariant P (chargeWasm m cost).1 := by
  cases m with
  | next c => exact chargeConfig_hostInvariant hcharge c cost h
  | done values store => exact ⟨h.1, hcharge store.host cost h.2⟩
  | trap reason store => exact ⟨h.1, hcharge store.host cost h.2⟩

theorem runMetered_hostInvariant (P : NearState → Prop)
    (hcharge : ∀ (ns : NearState) (cost : Nat), P ns → P (chargeHost ns cost).1)
    (cfg : WasmConfig) (fuel : Nat) (m : Machine) (h : MachineHostInvariant P m) :
    MachineHostInvariant P (runMetered cfg fuel m).1 := by
  induction fuel generalizing m with
  | zero => cases m <;> simpa only [runMetered] using h
  | succ fuel ih =>
    cases m with
    | done values store => simpa only [runMetered] using h
    | trap reason store => simpa only [runMetered] using h
    | next c =>
      have hp := chargeConfig_hostInvariant hcharge c (nextInstructionGas cfg c) h
      simp only [runMetered]
      split
      · exact hp
      · rename_i hnone
        have hn := step_hostInvariant hp
        have hfinal := chargeWasm_hostInvariant hcharge
          (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
          (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
            (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)) hn
        split
        · exact hfinal
        · exact ih _ hfinal

end Wasm.Near
