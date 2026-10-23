import NearVM.MeteredLiveInvariant

namespace Wasm.Near

/-- Unlike invariants required on every stop, a successful-execution invariant
may rely on gas charging succeeding. Exhaustion drops reserved gas and cannot
be treated as a live, financially backed execution. -/
theorem chargeConfig_success_liveInvariant {P : NearState → Prop}
    (hcharge : ∀ (ns : NearState) (cost : Nat),
      (chargeHost ns cost).2 = none → P ns → P (chargeHost ns cost).1)
    (c : Config NearState) (cost : Nat) (h : ConfigLiveInvariant P c)
    (hsuccess : (chargeConfig c cost).2 = none) :
    ConfigLiveInvariant P (chargeConfig c cost).1 :=
  ⟨h.1, hcharge c.store.host cost hsuccess h.2⟩

theorem chargeWasm_success_liveInvariant {P : NearState → Prop}
    (hcharge : ∀ (ns : NearState) (cost : Nat),
      (chargeHost ns cost).2 = none → P ns → P (chargeHost ns cost).1)
    (m : Machine) (cost : Nat) (h : MachineLiveInvariant P m)
    (hsuccess : (chargeWasm m cost).2 = none) :
    MachineLiveInvariant P (chargeWasm m cost).1 := by
  cases m with
  | next c => exact chargeConfig_success_liveInvariant hcharge c cost h hsuccess
  | done values store => exact ⟨h.1, hcharge store.host cost hsuccess h.2⟩
  | trap reason store => exact h

theorem runMetered_success_liveInvariant (P : NearState → Prop)
    (hcharge : ∀ (ns : NearState) (cost : Nat),
      (chargeHost ns cost).2 = none → P ns → P (chargeHost ns cost).1)
    (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : MachineLiveInvariant P m) (hsuccess : (runMetered cfg fuel m).2 = none) :
    MachineLiveInvariant P (runMetered cfg fuel m).1 := by
  induction fuel generalizing m with
  | zero => cases m <;> simpa only [runMetered] using h
  | succ fuel ih =>
    cases m with
    | done values store => simpa only [runMetered] using h
    | trap reason store => simpa only [runMetered] using h
    | next c =>
      simp only [runMetered] at hsuccess ⊢
      split at hsuccess
      · simp at hsuccess
      · rename_i hnone
        have hp := chargeConfig_success_liveInvariant hcharge c (nextInstructionGas cfg c) h hnone
        have hn := step_liveInvariant hp
        split at hsuccess
        · simp at hsuccess
        · rename_i hnone'
          have hfinal := chargeWasm_success_liveInvariant hcharge
            (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
            (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
              (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)) hn hnone'
          exact ih _ hfinal hsuccess

theorem runInitialized_success_liveInvariant (P : NearState → Prop)
    (hcharge : ∀ (ns : NearState) (cost : Nat),
      (chargeHost ns cost).2 = none → P ns → P (chargeHost ns cost).1)
    (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : MachineLiveInvariant P m) (hsuccess : (runInitialized cfg fuel m).2 = none) :
    MachineLiveInvariant P (runInitialized cfg fuel m).1 := by
  unfold runInitialized at hsuccess ⊢
  dsimp only at hsuccess ⊢
  split at hsuccess
  · simp at hsuccess
  · rename_i hnone
    have hp := chargeWasm_success_liveInvariant hcharge m (entryCost cfg m) h hnone
    exact runMetered_success_liveInvariant P hcharge cfg fuel _ hp hsuccess

theorem outcomeOfExecution_success_error_none (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : Machine) (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none) : error = none := by
  cases error with
  | none => rfl
  | some error => simp [outcomeOfExecution] at hsuccess

/-- Successful outcome packing rules out terminal traps. -/
theorem outcomeOfExecution_success_live {P : NearState → Prop}
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (final : Machine)
    (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (h : final.LiveHost P) : P final.host := by
  cases final with
  | next c => exact h
  | done values store => exact h
  | trap reason store =>
    cases error <;> simp [outcomeOfExecution] at hsuccess

end Wasm.Near
