import NearLogic.Resources

/-!
# Lifting a step that does not touch the host

Every Wasm instruction but a host call leaves the host state alone; its
metered step charges the gas counter twice (the instruction, then a new
frame's activation) and otherwise does what `Exec.step` does to the store.
`mwp_lift_plain` takes such a step from facts about `Exec.step` alone,
paying with credits: the rules of WasmLogic carry over with their side
conditions unchanged, plus their cost.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-! ## Charges that succeed -/

theorem burn_ok {g : Near.GasCounter} {n C : Nat} (h1 : g.used + n ≤ C) (h2 : C ≤ g.maxBurnt)
    (h3 : C ≤ g.prepaid) : g.burn n = ({ g with burnt := g.burnt + n }, none) := by
  unfold Near.GasCounter.burn Near.GasCounter.deduct
  unfold Near.GasCounter.used at h1
  rw [if_pos (by omega)]
  simp

/-- The host after a successful charge of `n`. -/
def charged (h : NearState) (n : Nat) : NearState :=
  { h with gas := { h.gas with burnt := h.gas.burnt + n },
           gasProfile := { h.gasProfile with wasm := h.gasProfile.wasm + n } }

theorem chargeHost_ok {h : NearState} {n C : Nat} (h1 : h.gas.used + n ≤ C) (h2 : C ≤ h.gas.maxBurnt)
    (h3 : C ≤ h.gas.prepaid) : chargeHost h n = (charged h n, none) := by
  unfold chargeHost charged
  rw [burn_ok h1 h2 h3]
  simp

theorem charged_charged (h : NearState) (a b : Nat) : charged (charged h a) b = charged h (a + b) := by
  simp [charged, Nat.add_assoc]

theorem erase_charged (h : NearState) (n : Nat) : erase (charged h n) = erase h := rfl

@[simp] theorem charged_gas_used (h : NearState) (n : Nat) :
    (charged h n).gas.used = h.gas.used + n := by
  simp [charged, Near.GasCounter.used]; omega

/-- The instruction cost does not look at the store. -/
theorem nextInstructionGas_store (cfg : WasmConfig) (s s' : Store NearState) (t : Thread)
    (lim : ExecLimits) :
    nextInstructionGas cfg { store := s, thread := t, limits := lim } =
      nextInstructionGas cfg { store := s', thread := t, limits := lim } := rfl

theorem gasCellOf_inj {g g' : Near.GasCounter} {p p' : Near.GasProfile}
    (h : gasCellOf g p = gasCellOf g' p') : g = g' ∧ p = p' := by
  unfold gasCellOf at h
  cases h
  exact ⟨rfl, rfl⟩

/-- The locations that are neither plain, the host nor the gas cell hold nothing. -/
theorem lookup_other (σ : Store NearState) {l : Loc} (hp : ¬ isPlain l) (hh : l ≠ Loc.host) :
    lookup σ l = none := by
  obtain ⟨k, a, i⟩ := l
  unfold isPlain at hp
  simp only at hp
  match k, a, i, hh with
  | 9, 0, 0, hh => exact absurd rfl hh
  | 9, _ + 1, _, _ | 9, 0, _ + 1, _ | _ + 10, _, _, _ => simp [lookup]
  | 0, _, _, _ | 1, _, _, _ | 2, _, _, _ | 3, _, _, _ | 4, _, _, _ | 5, _, _, _ | 6, _, _, _
  | 7, _, _, _ | 8, _, _, _ => omega

end NearLogic
