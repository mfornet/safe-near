import NearVM.CreationReservations
import NearVM.ExecutionReservations

namespace Wasm.Near

/-- Fixed billing inputs and outstanding raw obligations, excluding counters. -/
def reservationFrame (ns : NearState) : ActionFees × Bool × List NearPromise :=
  (ns.fees, ns.config.ethImplicitAccounts, ns.promises)

/-- The full observation needed by the gas-backing invariant. -/
def reservationView (ns : NearState) : (ActionFees × Bool × List NearPromise) × Nat :=
  (reservationFrame ns, ns.gas.promises)

theorem applyCharge_reservationFrame (ns : NearState) (charge : Charge) :
    reservationFrame (applyCharge ns charge).1 = reservationFrame ns := by
  cases charge <;> rfl

theorem applyCharges_reservationFrame (ns : NearState) (charges : List Charge) :
    reservationFrame (applyCharges ns charges).1 = reservationFrame ns := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge rest ih =>
    cases hc : applyCharge ns charge with
    | mk paid error =>
      have hp := applyCharge_reservationFrame ns charge
      rw [hc] at hp
      cases error with
      | some error => simpa only [applyCharges, hc] using hp
      | none => simpa only [applyCharges, hc] using (ih paid).trans hp

theorem ReservationInvariant.of_view_eq {fees : ActionFees} {ethEnabled : Bool} {before after : NearState}
    (hview : reservationView after = reservationView before)
    (h : ReservationInvariant fees ethEnabled before) : ReservationInvariant fees ethEnabled after := by
  have hf := congrArg (fun v => v.1.1) hview
  have he := congrArg (fun v => v.1.2.1) hview
  have hp := congrArg (fun v => v.1.2.2) hview
  have hg := congrArg Prod.snd hview
  change after.fees = before.fees at hf
  change after.config.ethImplicitAccounts = before.config.ethImplicitAccounts at he
  change after.promises = before.promises at hp
  change after.gas.promises = before.gas.promises at hg
  exact ⟨hf.trans h.1, he.trans h.2.1, by simpa only [GasBacked, hg, hp] using h.2.2⟩

/-- Successful charges with no onward obligation leave backing unchanged.
Failed charges may discard reserved gas and are intentionally excluded. -/
theorem applyCharges_success_zero_reservation (ns : NearState) (charges : List Charge)
    (hsuccess : (applyCharges ns charges).2 = none)
    (hzero : (charges.map (fun charge => charge.reservation ns.fees)).sum = 0) :
    reservationView (applyCharges ns charges).1 = reservationView ns := by
  have hg := applyCharges_success_reservation ns charges hsuccess
  simp only [hzero, Nat.add_zero] at hg
  exact Prod.ext (applyCharges_reservationFrame ns charges) hg

theorem writeReg_reservation (fees : ActionFees) (n : Nat) :
    ((writeReg n).map (fun charge => charge.reservation fees)).sum = 0 := by
  simp [writeReg, Charge.reservation]

/-- Every post-call charge is local burn; it cannot create an unbacked receipt. -/
theorem chargesAfter_reservation (fees : ActionFees) (name : String) (before after : Store NearState)
    (args : List Value) :
    ((chargesAfter name before after args).map (fun charge => charge.reservation fees)).sum = 0 := by
  unfold chargesAfter
  repeat' (first | rfl | split | (dsimp only; split))

theorem deductDeposit_reservationView (name : String) (before after : Store NearState) (args : List Value) :
    reservationView (deductDeposit name before after args).1.host = reservationView after.host := by
  unfold deductDeposit deductPromiseDeposit
  repeat' (first | rfl | split | (dsimp only; split))

theorem updateStorageUsage_reservationView (extra : Nat) (name : String) (before after : Store NearState)
    (args : List Value) :
    reservationView (updateStorageUsage extra name before after args).host = reservationView after.host := by
  unfold updateStorageUsage
  repeat' (first | rfl | split | (dsimp only; split))

/-- Post-call metering, deposit deductions (including the one-yocto subsidy),
and storage usage preserve backing on every nonterminal result. -/
theorem finishMeteredCall_reservationInvariant (fees : ActionFees) (ethEnabled : Bool)
    (extra : Nat) (name : String) (before : Store NearState) (args : List Value) (result : HostResult NearState)
    (hraw : HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled) result) :
    HostResult.LiveSatisfies (ReservationInvariant fees ethEnabled) (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st message => trivial
  | Throw st tag values => exact hraw
  | Return values st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk paid error =>
      cases error with
      | some error => trivial
      | none =>
        have hv := applyCharges_success_zero_reservation st.host (chargesAfter name before st args)
          (by rw [hc]) (chargesAfter_reservation st.host.fees name before st args)
        rw [hc] at hv
        have hp := ReservationInvariant.of_view_eq hv hraw
        cases hd : deductDeposit name before { st with host := paid } args with
        | mk final error =>
          cases error with
          | some error => trivial
          | none =>
            have hvd := deductDeposit_reservationView name before { st with host := paid } args
            rw [hd] at hvd
            exact ReservationInvariant.of_view_eq (updateStorageUsage_reservationView extra name before final args)
              (ReservationInvariant.of_view_eq hvd hp)

end Wasm.Near
