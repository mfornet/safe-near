import NearVM.Charge
import NearVM.GasCredits

/-!
# Sufficient credits for host burn charges

The M2 hosts use external-cost and direct burn charges. This file threads
credits through their actual charge lists, with exact burn and no promise
reservation changes. Action/promise charges are intentionally excluded.
-/
namespace Wasm.Near.MeteredHosts

/-- The charges whose entire cost is burnt. -/
def BurnsOnly : Charge → Prop
  | .ext .. | .burn .. => True
  | _ => False

/-- Cost of a burn-only charge; the premise `BurnsOnly` excludes other cases. -/
def burnCost (costs : ExtCosts) : Charge → Nat
  | .ext name times => costs.cost name * times
  | .burn n => n
  | _ => 0

def burnSum (costs : ExtCosts) (charges : List Charge) : Nat :=
  (charges.map (burnCost costs)).sum

/-- Exact gas and residual reservation for one actual host charge. -/
theorem applyCharge_credits (ns : NearState) (charge : Charge) (rest : Nat)
    (hburn : BurnsOnly charge)
    (hcredits : ns.gas.Credits (burnCost ns.extCosts charge + rest)) :
    (applyCharge ns charge).2 = none ∧
    (applyCharge ns charge).1.gas.burnt = ns.gas.burnt + burnCost ns.extCosts charge ∧
    (applyCharge ns charge).1.gas.promises = ns.gas.promises ∧
    (applyCharge ns charge).1.extCosts = ns.extCosts ∧
    (applyCharge ns charge).1.gas.Credits rest := by
  cases charge <;> simp only [BurnsOnly] at hburn
  case ext name times =>
    have h := GasCounter.burn_credits ns.gas (ns.extCosts.cost name * times) rest hcredits
    exact ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2⟩
  case burn n =>
    have h := GasCounter.burn_credits ns.gas n rest hcredits
    exact ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2⟩
  all_goals contradiction

/-- Sufficient credits discharge an entire host burn list. They are retained
as a frame and charged using the unchanged external-cost table. -/
theorem applyCharges_credits (ns : NearState) (charges : List Charge) (rest : Nat)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge)
    (hcredits : ns.gas.Credits (burnSum ns.extCosts charges + rest)) :
    (applyCharges ns charges).2 = none ∧
    (applyCharges ns charges).1.gas.burnt = ns.gas.burnt + burnSum ns.extCosts charges ∧
    (applyCharges ns charges).1.gas.promises = ns.gas.promises ∧
    (applyCharges ns charges).1.extCosts = ns.extCosts ∧
    (applyCharges ns charges).1.gas.Credits rest := by
  induction charges generalizing ns with
  | nil => exact ⟨rfl, by simp [applyCharges, burnSum], rfl, rfl, by simpa [burnSum, applyCharges] using hcredits⟩
  | cons charge charges ih =>
    have hc := applyCharge_credits ns charge (burnSum ns.extCosts charges + rest)
      (hburn charge (by simp)) (by simpa [burnSum, Nat.add_assoc] using hcredits)
    have hpair : applyCharge ns charge = ((applyCharge ns charge).1, none) := by
      exact Prod.ext rfl hc.1
    have ht := ih (applyCharge ns charge).1
      (fun c h => hburn c (by simp [h])) (by simpa only [hc.2.2.2.1] using hc.2.2.2.2)
    simp only [applyCharges]
    rw [hpair]
    refine ⟨ht.1, ?_, ht.2.2.1.trans hc.2.2.1, ht.2.2.2.1.trans hc.2.2.2.1, ht.2.2.2.2⟩
    rw [ht.2.1, hc.2.1, hc.2.2.2.1]
    simp [burnSum, Nat.add_assoc]

end Wasm.Near.MeteredHosts
