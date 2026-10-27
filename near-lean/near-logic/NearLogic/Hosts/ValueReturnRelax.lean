import NearLogic.Hosts.ValueReturn
import NearLogic.Relax

/-!
# `value_return` under raised gas limits

With the value in memory and within the return limit, metered
`value_return` either fails a charge (a gas error) or, run on the host with
raised limits, gives the same result with those limits.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A host result with its host's limits raised. -/
def _root_.Wasm.HostResult.relax (p m : Nat) : HostResult NearState → HostResult NearState
  | .Return vals st => .Return vals (relaxSt st p m)
  | .Trap st msg => .Trap (relaxSt st p m) msg

theorem valueReturn_relax (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) (p m : Nat)
    (hlen : len ≠ u64Max) (hin : ptr.toNat + len.toNat ≤ st.mem.size * 65536)
    (hlim : withinLimit st.host.config.maxReturnLen len.toNat = true)
    (hp : st.host.gas.prepaid ≤ p) (hm : st.host.gas.maxBurnt ≤ m) :
    (∃ st' e, (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
        trapWith st' e ∧ isGasError e) ∨
      (metered extra "value_return" valueReturnFn).invoke (relaxSt st p m) [.i64 len, .i64 ptr] =
        ((metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr]).relax p m := by
  have hcs := valueReturnCharges_eq st len ptr hlen hin hlim
  have hcs' : valueReturnCharges (relaxSt st p m) len ptr = valueReturnChargeList st.host len.toNat :=
    valueReturnCharges_eq (relaxSt st p m) len ptr hlen hin hlim
  have hdep : deprecatedRuntimeHost "value_return" = false := by decide
  have hview : viewRestrictedHost "value_return" = false := by decide
  have hget : getMemOrReg st ptr len = some (st.mem.readList ptr.toNat len.toNat) := by
    simp only [getMemOrReg, hlen, ite_false]
    rw [if_neg (by omega)]
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [show chargesBefore "value_return" st [.i64 len, .i64 ptr] = valueReturnCharges st len ptr from rfl,
    show chargesBefore "value_return" (relaxSt st p m) [.i64 len, .i64 ptr] =
      valueReturnCharges (relaxSt st p m) len ptr from rfl, hcs, hcs']
  cases hac : applyCharges st.host (valueReturnChargeList st.host len.toNat) with
  | mk ns err =>
    cases err with
    | some e =>
      left
      exact ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac])⟩
    | none =>
      right
      have hrel := applyCharges_relax st.host (valueReturnChargeList st.host len.toNat) p m hp hm (by rw [hac])
      rw [hac] at hrel
      simp only [relaxSt] at hrel ⊢
      rw [hrel]
      simp only
      have hcfg : ns.config = st.host.config := by
        have := applyCharges_gas_config st.host (valueReturnChargeList st.host len.toNat)
        rw [hac] at this
        exact this
      have hv : withinLimit ns.config.maxReturnLen (st.mem.readList ptr.toNat len.toNat).length = true := by
        rw [Memory.readList_length, hcfg]; exact hlim
      have hgm : ∀ s' : HostStore NearState, s'.mem = st.mem →
          getMemOrReg s' ptr len = some (st.mem.readList ptr.toNat len.toNat) := fun s' h => by
        rw [getMemOrReg_mem (s := st) (s' := s') hlen h, hget]
      -- Open: both sides run `preInvokeError_valueReturn` and `valueReturn_after` on the same
      -- memory; the rewrite does not match the stores `simp` leaves (to finish with lean_goal).
      sorry

end NearLogic
