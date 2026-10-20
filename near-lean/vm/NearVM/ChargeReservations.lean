import NearVM.GasInvariants

namespace Wasm.Near

/-- Execution/prepaid gas owed onward by one charge. Sending and dependency-data
fees are burnt locally; only the new action receipt's execution is reserved. -/
def Charge.reservation (fees : ActionFees) : Charge → Nat
  | .ext .. | .burn .. => 0
  | .actionBase fee _ => (fee fees).execution
  | .actionBytes fee count _ => (fee fees).execution * count
  | .newReceipt .. => fees.newActionReceipt.execution
  | .prepay gas => gas

@[simp] theorem applyCharge_fees (ns : NearState) (charge : Charge) :
    (applyCharge ns charge).1.fees = ns.fees := by
  cases charge <;> rfl

/-- Successful charging adds exactly the executable reservation amount. -/
theorem applyCharge_success_reservation (ns : NearState) (charge : Charge)
    (hsuccess : (applyCharge ns charge).2 = none) :
    (applyCharge ns charge).1.gas.promises = ns.gas.promises + charge.reservation ns.fees := by
  cases charge with
  | ext name count =>
    have h := GasCounter.deduct_success ns.gas (ns.extCosts.cost name * count)
      (ns.extCosts.cost name * count) (Nat.le_refl _) hsuccess
    simpa only [applyCharge, GasCounter.burn, Charge.reservation, Nat.sub_self, Nat.add_zero] using h.2.1
  | burn gas =>
    have h := GasCounter.deduct_success ns.gas gas gas (Nat.le_refl _) hsuccess
    simpa only [applyCharge, GasCounter.burn, Charge.reservation, Nat.sub_self, Nat.add_zero] using h.2.1
  | actionBase fee sir =>
    have h := GasCounter.deduct_success ns.gas ((fee ns.fees).send sir)
      ((fee ns.fees).send sir + (fee ns.fees).execution) (Nat.le_add_right _ _) hsuccess
    simpa only [applyCharge, GasCounter.payAction, Charge.reservation, Nat.add_sub_cancel_left] using h.2.1
  | actionBytes fee count sir =>
    have h := GasCounter.deduct_success ns.gas ((fee ns.fees).send sir * count)
      ((fee ns.fees).send sir * count + (fee ns.fees).execution * count) (Nat.le_add_right _ _) hsuccess
    simpa only [applyCharge, GasCounter.payAction, Charge.reservation, Nat.add_sub_cancel_left] using h.2.1
  | newReceipt sir deps =>
    let burnt := ns.fees.newActionReceipt.send sir +
      (deps.map fun same => ns.fees.newDataReceiptBase.send same + ns.fees.newDataReceiptBase.execution).sum
    have h := GasCounter.deduct_success ns.gas burnt (burnt + ns.fees.newActionReceipt.execution)
      (Nat.le_add_right _ _) hsuccess
    simpa only [applyCharge, GasCounter.payAction, Charge.reservation, Nat.add_sub_cancel_left] using h.2.1
  | prepay gas =>
    have h := GasCounter.deduct_success ns.gas 0 gas (Nat.zero_le _) hsuccess
    simpa only [applyCharge, GasCounter.prepay, Charge.reservation, Nat.sub_zero] using h.2.1

/-- A successful whole charge plan reserves its full sum, without an assumed
counter equation. Failed prefixes are excluded explicitly. -/
theorem applyCharges_success_reservation (ns : NearState) (charges : List Charge)
    (hsuccess : (applyCharges ns charges).2 = none) :
    (applyCharges ns charges).1.gas.promises =
      ns.gas.promises + (charges.map (fun charge => charge.reservation ns.fees)).sum := by
  induction charges generalizing ns with
  | nil => simp [applyCharges]
  | cons charge rest ih =>
    cases hc : applyCharge ns charge with
    | mk paid error =>
      cases error with
      | some error => simp only [applyCharges, hc, reduceCtorEq] at hsuccess
      | none =>
        have hp := applyCharge_success_reservation ns charge (by rw [hc])
        have hf := applyCharge_fees ns charge
        rw [hc] at hp hf
        dsimp only at hp hf
        have hr := ih paid (by simpa only [applyCharges, hc] using hsuccess)
        rw [hf] at hr
        simp only [applyCharges, hc, List.map_cons, List.sum_cons]
        rw [hr, hp]
        exact Nat.add_assoc _ _ _

end Wasm.Near
