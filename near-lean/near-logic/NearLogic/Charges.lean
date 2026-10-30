import NearLogic.Lift

/-!
# Host charges within credits

A host function charges a list of `Charge`s (`Wasm.Near.applyCharges`)
before and after it runs. Each charge raises `used` by an amount fixed by
the fee tables (`chargeUse`); when the total fits the credits, every charge
succeeds, and only the gas cell changes: the counter and the two profiles.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- How much a charge raises `used`, from the fee tables. -/
def chargeUse (ns : NearState) : Charge → Nat
  | .ext name times => ns.extCosts.cost name * times
  | .burn n => n
  | .actionBase fee sir => (fee ns.fees).send sir + (fee ns.fees).execution
  | .actionBytes fee n sir => (fee ns.fees).send sir * n + (fee ns.fees).execution * n
  | .newReceipt sir depsSir =>
    (ns.fees.newActionReceipt.send sir +
      (depsSir.map fun s => ns.fees.newDataReceiptBase.send s + ns.fees.newDataReceiptBase.execution).sum) +
    ns.fees.newActionReceipt.execution
  | .prepay n => n
  | .pay burn execution => burn + execution

def chargesUse (ns : NearState) (cs : List Charge) : Nat := (cs.map (chargeUse ns)).sum

theorem deduct_ok {g : Near.GasCounter} {burn use C : Nat} (hb : burn ≤ use) (h1 : g.used + use ≤ C)
    (h2 : C ≤ g.maxBurnt) (h3 : C ≤ g.prepaid) :
    g.deduct burn use = ({ g with burnt := g.burnt + burn, promises := g.promises + (use - burn) }, none) := by
  unfold Near.GasCounter.deduct
  unfold Near.GasCounter.used at h1
  rw [if_pos (by omega)]

/-- A charge within the credits: what it leaves. -/
structure ChargedTo (ns ns' : NearState) (n : Nat) : Prop where
  used : ns'.gas.used = ns.gas.used + n
  maxBurnt : ns'.gas.maxBurnt = ns.gas.maxBurnt
  prepaid : ns'.gas.prepaid = ns.gas.prepaid
  erase : erase ns' = erase ns
  fees : ns'.fees = ns.fees
  extCosts : ns'.extCosts = ns.extCosts
  config : ns'.config = ns.config

theorem applyCharge_ok (ns : NearState) (c : Charge) {C : Nat} (h1 : ns.gas.used + chargeUse ns c ≤ C)
    (h2 : C ≤ ns.gas.maxBurnt) (h3 : C ≤ ns.gas.prepaid) :
    (applyCharge ns c).2 = none ∧ ChargedTo ns (applyCharge ns c).1 (chargeUse ns c) := by
  cases c with
  | ext name times =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.burn, deduct_ok (Nat.le_refl _) h1 h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, Near.GasCounter.used]; omega
  | burn n =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.burn, deduct_ok (Nat.le_refl _) h1 h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, NearState.profileAction, Near.GasCounter.used]; omega
  | actionBase fee sir =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.payAction, deduct_ok (Nat.le_add_right _ _) h1 h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, NearState.profileAction, Near.GasCounter.used]; omega
  | actionBytes fee n sir =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.payAction, deduct_ok (Nat.le_add_right _ _) h1 h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, NearState.profileAction, Near.GasCounter.used]; omega
  | newReceipt sir depsSir =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.payAction, deduct_ok (Nat.le_add_right _ _) h1 h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, NearState.profileAction, Near.GasCounter.used]; omega
  | prepay n =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.prepay, deduct_ok (Nat.zero_le _) (by simpa using h1) h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, Near.GasCounter.used]; omega
  | pay burn execution =>
    simp only [chargeUse] at h1
    simp only [applyCharge, Near.GasCounter.payAction, deduct_ok (Nat.le_add_right _ _) h1 h2 h3]
    refine ⟨by first | rfl | trivial, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    simp [chargeUse, NearState.profileAction, Near.GasCounter.used]; omega

theorem chargeUse_congr {ns ns' : NearState} (hf : ns'.fees = ns.fees) (he : ns'.extCosts = ns.extCosts)
    (c : Charge) : chargeUse ns' c = chargeUse ns c := by
  cases c <;> simp [chargeUse, hf, he]

/-- Charges within the credits all succeed, and only the gas cell changes. -/
theorem applyCharges_ok (ns : NearState) (cs : List Charge) {C : Nat}
    (h1 : ns.gas.used + chargesUse ns cs ≤ C) (h2 : C ≤ ns.gas.maxBurnt) (h3 : C ≤ ns.gas.prepaid) :
    (applyCharges ns cs).2 = none ∧ ChargedTo ns (applyCharges ns cs).1 (chargesUse ns cs) := by
  induction cs generalizing ns with
  | nil => exact ⟨rfl, ⟨by simp [chargesUse, applyCharges], rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | cons c cs ih =>
    simp only [chargesUse, List.map_cons, List.sum_cons] at h1
    obtain ⟨he, hc⟩ := applyCharge_ok ns c (C := C) (by omega) h2 h3
    have hcs : chargesUse (applyCharge ns c).1 cs = chargesUse ns cs := by
      unfold chargesUse
      congr 1
      exact List.map_congr_left fun c _ => chargeUse_congr hc.fees hc.extCosts c
    obtain ⟨he', hc'⟩ := ih (applyCharge ns c).1
      (by rw [hcs, hc.used]; simp only [chargesUse] at h1 ⊢; omega)
      (by rw [hc.maxBurnt]; exact h2) (by rw [hc.prepaid]; exact h3)
    simp only [applyCharges]
    rw [show applyCharge ns c = ((applyCharge ns c).1, none) by rw [← he]]
    simp only
    refine ⟨he', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hc'.used, hcs, hc.used]; simp [chargesUse]; omega
    · rw [hc'.maxBurnt, hc.maxBurnt]
    · rw [hc'.prepaid, hc.prepaid]
    · rw [hc'.erase, hc.erase]
    · rw [hc'.fees, hc.fees]
    · rw [hc'.extCosts, hc.extCosts]
    · rw [hc'.config, hc.config]

end NearLogic
