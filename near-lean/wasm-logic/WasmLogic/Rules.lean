import WasmLogic.Language
import Iris.ProgramLogic.OwnP

/-!
# Weakest-precondition rules

Store ownership (`ownP σ`) is the resource; the rules follow the machine one
step at a time, or a whole run. Because the step is a function, every rule is
deterministic: the successor configuration is computed, not quantified over.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
  Iris.ProgramLogic.PrimStep FromMathlib Std.LawfulSet

variable {H : Type} {GF : BundledGFunctors} [OwnPGS (Store H) GF]
variable {s : Stuckness} {E : CoPset} {Φ : Outcome → IProp GF}

/-- A running thread is never stuck, whatever the stuckness. -/
theorem running_safe (limits : ExecLimits) (thread : Thread) (σ : Store H) :
    ReducibleOrNotVal (Val := Outcome) s (Code.running limits thread, σ) := by
  cases s
  · exact running_reducible limits thread σ
  · rfl

/-- One step that keeps running. -/
theorem wp_step (σ : Store H) (limits : ExecLimits) (thread : Thread) (c' : Config H)
    (h : Exec.step (Code.config σ limits thread) = .next c') :
    ▷ ownP σ ∗
      ▷ (ownP c'.store -∗ WP (Code.running (H := H) limits c'.thread) @ s; E {{ Φ }})
      ⊢ WP (Code.running (H := H) limits thread) @ s; E {{ Φ }} := by
  have hn : next σ limits thread = (.running limits c'.thread, c'.store) := by
    simp [next, h]
  iintro ⟨Hσ, H⟩
  iapply ownP_lift_step
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  iexists σ
  have Hsafe := running_safe (s := s) limits thread σ
  iframe Hσ %Hsafe
  iintro !> %obs %e₂ %σ₂ %eₜ %Hstep Hσ₂
  obtain ⟨rfl, rfl, rfl, rfl⟩ := step_det Hstep
  rw [hn]
  imod Hclose
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  isplitl [H Hσ₂]
  · iapply H $$ Hσ₂
  · itrivial

/-- One step that finishes with values. -/
theorem wp_done (σ : Store H) (limits : ExecLimits) (thread : Thread) (vs : List Value)
    (s' : Store H) (h : Exec.step (Code.config σ limits thread) = .done vs s') :
    {{ ▷ ownP (GF := GF) σ }} (Code.running (H := H) limits thread) @ s; E
      {{ RET Outcome.values vs; ownP s' }} :=
  ownP_lift_atomic_det_step_no_fork (running_safe limits thread σ) fun hstep => by
    obtain ⟨-, rfl, rfl, rfl⟩ := step_det hstep
    simp [next, h]
    rfl

/-- One step that traps. -/
theorem wp_trap (σ : Store H) (limits : ExecLimits) (thread : Thread) (r : Trap)
    (s' : Store H) (h : Exec.step (Code.config σ limits thread) = .trap r s') :
    {{ ▷ ownP (GF := GF) σ }} (Code.running (H := H) limits thread) @ s; E
      {{ RET Outcome.trap r; ownP s' }} :=
  ownP_lift_atomic_det_step_no_fork (running_safe limits thread σ) fun hstep => by
    obtain ⟨-, rfl, rfl, rfl⟩ := step_det hstep
    simp [next, h]
    rfl

/-- A whole run that finishes: own the store before, get the final store back. -/
theorem wp_run (fuel : Nat) (σ : Store H) (limits : ExecLimits) (thread : Thread)
    (vs : List Value) (s' : Store H)
    (h : Exec.run fuel (Code.config σ limits thread) = .done vs s') :
    ownP σ ∗ (ownP s' -∗ Φ (.values vs)) ⊢
      WP (Code.running (H := H) limits thread) @ s; E {{ Φ }} := by
  induction fuel generalizing σ thread with
  | zero => simp [Exec.run] at h
  | succ fuel ih =>
    unfold Exec.run at h
    cases hc : Exec.step (Code.config σ limits thread) with
    | next c =>
      rw [hc] at h
      have hl := Exec.step_limits _ hc
      have hc' : Code.config c.store limits c.thread = c := by
        cases c; simp_all [Code.config]
      iintro ⟨Hσ, HΦ⟩
      iapply wp_step σ limits thread c hc
      isplitl [Hσ]
      · iapply later_intro; iexact Hσ
      · iapply later_intro
        iintro Hσ'
        iapply ih c.store c.thread (hc' ▸ h) $$ [$Hσ' $HΦ]
    | done vs' s'' =>
      rw [hc] at h
      cases h
      iintro ⟨Hσ, HΦ⟩
      iapply wp_done σ limits thread vs s' hc $$ [$Hσ] [$HΦ]
    | trap r s'' =>
      rw [hc] at h
      cases h

end WasmLogic
