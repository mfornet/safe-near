import NearLogic.Hosts.ValueReturnRelax

/-!
# The metered wrapper under raised gas limits

`metered_relax`: a metered host function respects raised limits when its
three parts do, each on its own: the charges before the call
(`chargesBefore`) and the argument check (`preInvokeError`) do not look at
the limits, and the call itself (`invokeStorageCall`: the storage phase,
the functional host and the charges after it) either fails a charge or
commutes with raising the limits. The view-restricted and deprecated
branches are handled here once.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A host result that is a failed charge: a trap recording a gas error. -/
def GasTrapResult (r : HostResult NearState) : Prop :=
  ∃ st e, r = trapWith st e ∧ isGasError e

theorem trapWith_relax (st : HostStore NearState) (e : HostError) (p m : Nat) :
    trapWith (relaxSt st p m) e = (trapWith st e).relax p m := rfl

/-- The call after the charges before it respects raised limits. -/
def InvokeRelax (extra : Nat) (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    st.host.gas.prepaid ≤ p → st.host.gas.maxBurnt ≤ m →
    GasTrapResult (invokeStorageCall extra name fn st args) ∨
      invokeStorageCall extra name fn (relaxSt st p m) args = (invokeStorageCall extra name fn st args).relax p m

/-- **The metered wrapper respects raised limits** when its parts do. -/
theorem metered_relax (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hcb : ∀ st args p m, chargesBefore name (relaxSt st p m) args = chargesBefore name st args)
    (hpre : ∀ st args p m, preInvokeError name (relaxSt st p m) args = preInvokeError name st args)
    (hinv : InvokeRelax extra name fn)
    (st : HostStore NearState) (args : List Value) (p m : Nat)
    (hp : st.host.gas.prepaid ≤ p) (hm : st.host.gas.maxBurnt ≤ m) :
    GasTrapResult ((metered extra name fn).invoke st args) ∨
      (metered extra name fn).invoke (relaxSt st p m) args = ((metered extra name fn).invoke st args).relax p m := by
  have hctx : (relaxSt st p m).host.context = st.host.context := rfl
  simp only [metered]
  rw [hctx]
  by_cases hdep : deprecatedRuntimeHost name = true
  · right; simp only [hdep, ite_true]; rfl
  simp only [hdep, Bool.false_eq_true, ite_false]
  by_cases hview : (st.host.context.isView && viewRestrictedHost name) = true
  · simp only [hview, ite_true]
    generalize (([.ext "base"] ++ (if name == "promise_return" then [.ext "promise_return"] else [])) :
      List Charge) = cs
    rw [show (relaxSt st p m).host = relax st.host p m from rfl]
    cases hac : applyCharges st.host cs with
    | mk ns err =>
      cases err with
      | some e =>
        left
        exact ⟨{ st with host := ns }, e, rfl, applyCharges_error _ _ (by rw [hac])⟩
      | none =>
        right
        have hrel := applyCharges_relax st.host cs p m hp hm (by rw [hac])
        rw [hac] at hrel
        rw [hrel]
        rfl
  simp only [hview, Bool.false_eq_true, ite_false]
  rw [hcb, show (relaxSt st p m).host = relax st.host p m from rfl]
  cases hac : applyCharges st.host (chargesBefore name st args) with
  | mk ns err =>
    have hlims := applyCharges_gas_limits st.host (chargesBefore name st args)
    rw [hac] at hlims
    cases err with
    | some e =>
      left
      exact ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac])⟩
    | none =>
      have hrel := applyCharges_relax st.host (chargesBefore name st args) p m hp hm (by rw [hac])
      rw [hac] at hrel
      rw [hrel]
      -- The store after the charges.
      let st1 : HostStore NearState :=
        { st with host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have htail : GasTrapResult (match preInvokeError name st1 args with
          | some error => trapWith st1 error
          | none => invokeStorageCall extra name fn st1 args) ∨
          (match preInvokeError name (relaxSt st1 p m) args with
            | some error => trapWith (relaxSt st1 p m) error
            | none => invokeStorageCall extra name fn (relaxSt st1 p m) args) =
          (match preInvokeError name st1 args with
            | some error => trapWith st1 error
            | none => invokeStorageCall extra name fn st1 args).relax p m := by
        rw [hpre]
        cases preInvokeError name st1 args with
        | some e => right; rfl
        | none =>
          exact hinv st1 args p m (by show ns.gas.prepaid ≤ p; rw [hlims.1]; exact hp)
            (by show ns.gas.maxBurnt ≤ m; rw [hlims.2]; exact hm)
      exact htail

end NearLogic
