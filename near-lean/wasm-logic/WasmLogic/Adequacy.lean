import WasmLogic.Language
import Iris.ProgramLogic.OwnP
import Iris.Examples.ClosedProofs

/-!
# Adequacy: from a weakest precondition to the executable semantics

A closed resource family `GF` with the invariant and later-credit slots that
`iris-lean` needs plus one slot owning the store. With it, a proof that
`ownP σ` entails a weakest precondition with a pure postcondition turns into
a statement about `Wasm.Exec.run`: whenever the machine finishes, the outcome
satisfies the postcondition.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib COFE
  HeapView Auth Std.LawfulSet

/-- The resource functors: iris-lean's four bookkeeping slots, then store ownership. -/
noncomputable def GF (H : Type) : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨ownPRF (Store H), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance (H : Type) : WsatGpreS (GF H) where
  inv := { τ := 0, transp := by unfold GF; rfl }
  enabled := { τ := 1, transp := by unfold GF; rfl }
  disabled := { τ := 2, transp := by unfold GF; rfl }

instance (H : Type) : LcGpreS (GF H) where
  lc_elem := { τ := 3, transp := by unfold GF; rfl }

instance (H : Type) : InvGpreS (GF H) where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance (H : Type) : OwnPGpreS (Store H) (GF H) where
  inG := { τ := 4, transp := by unfold GF; rfl }

/-- What a run of the machine can end in, as the language sees it. -/
theorem run_outcome (fuel : Nat) (σ : Store H) (limits : ExecLimits) (thread : Thread)
    (φ : Outcome → Prop)
    (had : adequate (Expr := Code H) .MaybeStuck (.running limits thread) σ (fun o _ => φ o)) :
    match Exec.run fuel (Code.config σ limits thread) with
    | .done vs _ => φ (.values vs)
    | .trap r _ => φ (.trap r)
    | .outOfFuel _ => True := by
  have steps := run_steps fuel σ limits thread
  cases h : Exec.run fuel (Code.config σ limits thread) with
  | done vs s =>
    rw [h] at steps
    exact had.adequate_result [] s (.values vs) steps
  | trap r s =>
    rw [h] at steps
    exact had.adequate_result [] s (.trap r) steps
  | outOfFuel _ => trivial

/-- Adequacy for the Wasm machine: a weakest precondition proved from store
ownership holds of every finished run. -/
theorem adequacy (σ : Store H) (limits : ExecLimits) (thread : Thread) (φ : Outcome → Prop)
    (hwp : ∀ [OwnPGS (Store H) (GF H)],
      ownP (GF := GF H) σ ⊢
        WP (Code.running (H := H) limits thread) @ Stuckness.MaybeStuck; ⊤ {{ o, ⌜φ o⌝ }})
    (fuel : Nat) :
    match Exec.run fuel (Code.config σ limits thread) with
    | .done vs _ => φ (.values vs)
    | .trap r _ => φ (.trap r)
    | .outOfFuel _ => True :=
  run_outcome fuel σ limits thread φ (ownP_adequacy (GF := GF H) _ _ _ _ hwp)

end WasmLogic
