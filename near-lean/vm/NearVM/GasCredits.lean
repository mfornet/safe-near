import NearInterface.Gas
import Lean.Elab.Tactic.Omega

/-!
# Credits for metered contracts

Credits reserve room under both limits: irreversible burn and total gas
(including promises). They are logical resources; allocating credits never
changes prepaid gas or any value a Wasm host function can observe.
-/

namespace Wasm.Near.GasCounter

/-- Room to burn `n` gas without exceeding either protocol limit. -/
def Credits (g : GasCounter) (n : Nat) : Prop :=
  g.burnt + n ≤ g.maxBurnt ∧ g.used + n ≤ g.prepaid

theorem Credits.mono {g : GasCounter} {n k : Nat} (h : g.Credits n) (hk : k ≤ n) :
    g.Credits k := by
  unfold Credits at *
  omega

/-- The exact precondition for a successful burn, including equality at a limit. -/
theorem burn_ok_iff (g : GasCounter) (n : Nat) :
    (g.burn n).2 = none ↔ g.Credits n := by
  simp only [burn, deduct, Nat.sub_self, Nat.add_zero, Credits, used]
  split <;> simp_all <;> omega

/-- Spending part of a reservation leaves the rest available, including a
caller-owned frame of credits. No promise reservation is lost. -/
theorem burn_credits (g : GasCounter) (n rest : Nat) (h : g.Credits (n + rest)) :
    (g.burn n).2 = none ∧
    (g.burn n).1.burnt = g.burnt + n ∧
    (g.burn n).1.promises = g.promises ∧
    (g.burn n).1.Credits rest := by
  have hlimits : g.burnt + n ≤ g.maxBurnt ∧
      g.burnt + n + (g.promises + (n - n)) ≤ g.prepaid := by
    unfold Credits used at h
    omega
  unfold burn deduct
  rw [ite_eq_left hlimits]
  exact ⟨rfl, rfl, by simp, by unfold Credits used at *; dsimp only; omega⟩

/-- Reserving promise gas consumes prepaid capacity without consuming burn
capacity. The same credit frame therefore survives the reservation. -/
theorem prepay_credits (g : GasCounter) (n rest : Nat) (h : g.Credits (n + rest)) :
    (g.prepay n).2 = none ∧ (g.prepay n).1.burnt = g.burnt ∧
    (g.prepay n).1.promises = g.promises + n ∧
    (g.prepay n).1.Credits rest := by
  have hlimits : g.burnt + 0 ≤ g.maxBurnt ∧
      g.burnt + 0 + (g.promises + (n - 0)) ≤ g.prepaid := by
    unfold Credits used at h
    omega
  unfold prepay deduct
  rw [ite_eq_left hlimits]
  refine ⟨rfl, by simp, by simp, ?_⟩
  unfold Credits used at *
  dsimp only
  omega

/-- Charging a frame's entire allowance leaves a valid zero-credit counter. -/
theorem burn_all (g : GasCounter) (n : Nat) (h : g.Credits n) :
    (g.burn n).2 = none ∧ (g.burn n).1.Credits 0 := by
  have hr := burn_credits g n 0 (by simpa using h)
  exact ⟨hr.1, hr.2.2.2⟩

end Wasm.Near.GasCounter
