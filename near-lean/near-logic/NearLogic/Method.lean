import NearLogic.Adequacy
import NearLogic.Entry

/-!
# From a method's `WP` to `runInitialized`

`runAttempt` runs a method with `runInitialized`: the entry frame's
activation charge, then `runMetered`. `runInitialized_ending` reads how it
ends from adequacy of the metered language, once the activation is paid.
-/

namespace NearLogic

open Wasm Wasm.Near Iris.ProgramLogic

/-- How `runInitialized` ends, when the entry activation was paid and the
charged configuration satisfies `φ` by adequacy. -/
theorem runInitialized_ending (cfg : WasmConfig) (fuel : Nat) (c c' : Config NearState) (φ : Ending → Prop)
    (hentry : chargeWasm (.next c) (entryCost cfg (.next c)) = (.next c', none))
    (had : adequate (Expr := MCode) .MaybeStuck (.running cfg c'.limits c'.thread) ⟨c'.store⟩
      (fun v _ => φ v)) :
    match resultCode cfg (runInitialized cfg fuel (.next c)) with
    | (.finished e, _) => φ e
    | (.running .., _) => True := by
  have h : runInitialized cfg fuel (.next c) = runMetered cfg fuel (.next c') := by
    unfold runInitialized
    simp only [hentry]
  rw [h]
  exact runMetered_ending cfg fuel c' φ had

end NearLogic
