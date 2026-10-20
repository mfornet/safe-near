import NearVM.MeteredLiveInvariant

namespace Wasm.Near

/-- Unlike invariants required on every stop, a successful-execution invariant
may rely on gas charging succeeding. Exhaustion drops reserved gas and cannot
be treated as a live, financially backed execution. -/
theorem chargeWasm_success_liveInvariant {P : NearState → Prop}
    (hcharge : ∀ (config : SmallStep.Config NearState) (cost : Nat),
      (chargeWasm config cost).2 = none → P config.store.wasm.host → P (chargeWasm config cost).1.store.wasm.host)
    (config : SmallStep.Config NearState) (cost : Nat) (h : ConfigLiveInvariant P config)
    (hsuccess : (chargeWasm config cost).2 = none) :
    ConfigLiveInvariant P (chargeWasm config cost).1 := by
  refine ⟨h.1, ?_⟩
  have hl := h.2
  cases he : config.expr <;>
    simp only [SmallStep.Config.LiveHost, chargeWasm, he] at hl ⊢
  · exact hcharge config cost hsuccess hl
  · exact hcharge config cost hsuccess hl

theorem runMetered_success_liveInvariant (P : NearState → Prop)
    (hcharge : ∀ (config : SmallStep.Config NearState) (cost : Nat),
      (chargeWasm config cost).2 = none → P config.store.wasm.host → P (chargeWasm config cost).1.store.wasm.host)
    (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (h : ConfigLiveInvariant P config) (hsuccess : (runMetered cfg fuel config).2 = none) :
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
        cases error with
        | some error => simp only [runMetered, he, hc, reduceCtorEq] at hsuccess
        | none =>
          have hp := chargeWasm_success_liveInvariant hcharge config (nextInstructionGas cfg config) h (by rw [hc])
          rw [hc] at hp
          cases hs : SmallStep.stepChecked? paid with
          | error error => simp only [runMetered, he, hc, hs, reduceCtorEq] at hsuccess
          | ok transition =>
            cases transition with
            | none => simp only [runMetered, he, hc, hs, reduceCtorEq] at hsuccess
            | some transition =>
              obtain ⟨kind, next⟩ := transition
              have hn := step_preserves_liveInvariant (SmallStep.stepChecked?_sound hs) hp
              cases hf : chargeWasm next (frameTransitionGas cfg paid next) with
              | mk final error =>
                cases error with
                | some error => simp only [runMetered, he, hc, hs, hf, reduceCtorEq] at hsuccess
                | none =>
                  have hfinal := chargeWasm_success_liveInvariant hcharge next (frameTransitionGas cfg paid next) hn (by rw [hf])
                  rw [hf] at hfinal
                  have hsuc : (runMetered cfg fuel final).2 = none := by
                    simpa only [runMetered, he, hc, hs, hf] using hsuccess
                  simpa only [runMetered, he, hc, hs, hf] using ih final hfinal hsuc

theorem runInitialized_success_liveInvariant (P : NearState → Prop)
    (hcharge : ∀ (config : SmallStep.Config NearState) (cost : Nat),
      (chargeWasm config cost).2 = none → P config.store.wasm.host → P (chargeWasm config cost).1.store.wasm.host)
    (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (h : ConfigLiveInvariant P config) (hsuccess : (runInitialized cfg fuel config).2 = none) :
    ConfigLiveInvariant P (runInitialized cfg fuel config).1 := by
  unfold runInitialized at hsuccess ⊢
  dsimp only at hsuccess ⊢
  generalize hc : chargeWasm config (match config.expr with
    | .running thread => activationGas cfg.regularOpCost thread.locals
    | _ => 0) = charged at hsuccess ⊢
  obtain ⟨paid, error⟩ := charged
  cases error with
  | some error => simp only [reduceCtorEq] at hsuccess
  | none =>
    have hp := chargeWasm_success_liveInvariant hcharge config _ h (by rw [hc])
    rw [hc] at hp
    exact runMetered_success_liveInvariant P hcharge cfg fuel paid hp hsuccess

theorem outcomeOfExecution_success_error_none (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : SmallStep.Config NearState) (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none) : error = none := by
  cases error with
  | none => rfl
  | some error => simp [outcomeOfExecution] at hsuccess

/-- Successful outcome packing rules out terminal traps, including catchable
exceptions that escaped all handlers. -/
theorem outcomeOfExecution_success_live {P : NearState → Prop}
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (final : SmallStep.Config NearState)
    (error : Option FunctionCallError) (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (h : final.LiveHost P) : P final.store.wasm.host := by
  cases he : final.expr with
  | running thread => simpa only [SmallStep.Config.LiveHost, he] using h
  | done values => simpa only [SmallStep.Config.LiveHost, he] using h
  | trapped reason =>
    cases error <;> simp [outcomeOfExecution, he] at hsuccess

end Wasm.Near
