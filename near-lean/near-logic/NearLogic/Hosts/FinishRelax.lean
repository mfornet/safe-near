import NearLogic.Hosts.MeteredRelax

/-!
# The charges after a host call under raised gas limits

What `finishMeteredCall` reads of its stores (the charges after the call,
the deposit, the action encoding and the storage usage) does not depend on
the gas limits, so it commutes with raising them, unless a charge fails.
-/

namespace NearLogic

open Wasm Wasm.Near

theorem chargesAfter_relax (name : String) (before after : HostStore NearState) (args : List Value) (p m : Nat) :
    chargesAfter name (relaxSt before p m) (relaxSt after p m) args = chargesAfter name before after args := by
  rfl

theorem deductPromiseDeposit_relax (name : String) (ns : NearState) (d p m : Nat) :
    deductPromiseDeposit name (relax ns p m) d =
      (relax (deductPromiseDeposit name ns d).1 p m, (deductPromiseDeposit name ns d).2) := by
  unfold deductPromiseDeposit
  have hc : (relax ns p m).config = ns.config := rfl
  have hx : (relax ns p m).context = ns.context := rfl
  rw [hc, hx]
  dsimp only
  split_ifs <;> rfl

theorem deductDeposit_relax (name : String) (before after : HostStore NearState) (args : List Value) (p m : Nat) :
    deductDeposit name (relaxSt before p m) (relaxSt after p m) args =
      (relaxSt (deductDeposit name before after args).1 p m, (deductDeposit name before after args).2) := by
  unfold deductDeposit
  have hd : promiseDeposit? name (relaxSt before p m) args = promiseDeposit? name before args := rfl
  rw [hd]
  dsimp only
  cases promiseDeposit? name before args with
  | none => rfl
  | some d =>
    cases d with
    | zero => rfl
    | succ d =>
      rw [show (relaxSt after p m).host = relax after.host p m from rfl]
      simp only [deductPromiseDeposit_relax]
      rfl

theorem actionMethodEncodingError_relax (name : String) (before : HostStore NearState) (args : List Value)
    (p m : Nat) : actionMethodEncodingError name (relaxSt before p m) args = actionMethodEncodingError name before args := by
  rfl

theorem updateStorageUsage_relax (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) (p m : Nat) :
    updateStorageUsage extra name (relaxSt before p m) (relaxSt after p m) args =
      relaxSt (updateStorageUsage extra name before after args) p m := by
  unfold updateStorageUsage
  dsimp only
  have hg : getMemOrReg (relaxSt before p m) (argU64 args 1) (argU64 args 0) =
      getMemOrReg before (argU64 args 1) (argU64 args 0) := rfl
  split <;> (try rw [hg]) <;> (try split) <;> rfl

/-- `finishMeteredCall` under raised limits: a failed charge after the
call, or the same result with the limits raised. -/
theorem finishMeteredCall_relax (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (r : HostResult NearState) (p m : Nat)
    (hlim : ∀ vals st2, r = .Return vals st2 → st2.host.gas.prepaid ≤ p ∧ st2.host.gas.maxBurnt ≤ m) :
    GasTrapResult (finishMeteredCall extra name before args r) ∨
      finishMeteredCall extra name (relaxSt before p m) args (r.relax p m) =
        (finishMeteredCall extra name before args r).relax p m := by
  cases r with
  | Trap st2 msg => right; rfl
  | Return vals st2 =>
    obtain ⟨hp, hm⟩ := hlim vals st2 rfl
    simp only [finishMeteredCall, HostResult.relax]
    rw [chargesAfter_relax, show (relaxSt st2 p m).host = relax st2.host p m from rfl]
    cases hac : applyCharges st2.host (chargesAfter name before st2 args) with
    | mk ns err =>
      cases err with
      | some e =>
        left
        exact ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac])⟩
      | none =>
        right
        have hrel := applyCharges_relax st2.host (chargesAfter name before st2 args) p m hp hm (by rw [hac])
        rw [hac] at hrel
        rw [hrel]
        have hd := deductDeposit_relax name before { st2 with host := ns } args p m
        have hst : ({ mem := (relaxSt st2 p m).mem, host := relax ns p m } : HostStore NearState) =
            relaxSt { st2 with host := ns } p m := rfl
        simp only
        rw [hst, hd, actionMethodEncodingError_relax]
        cases hdd : deductDeposit name before { st2 with host := ns } args with
        | mk st4 e4 =>
          cases e4 with
          | some e => rfl
          | none =>
            simp only
            cases actionMethodEncodingError name before args with
            | some e => rfl
            | none => simp only [HostResult.relax]; rw [updateStorageUsage_relax]

/-- The call of a host function that is not a storage operation respects
raised limits when the functional host commutes with raising them and
keeps the limits. -/
theorem invokeRelax_plain (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hns : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains name = false)
    (hfn : ∀ st args p m, fn.invoke (relaxSt st p m) args = (fn.invoke st args).relax p m)
    (hkeep : ∀ st args vals st2, fn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt) :
    InvokeRelax extra name fn := by
  intro st args p m hp hm
  simp only [invokeStorageCall, prepareStorageCall_other name st args hns,
    prepareStorageCall_other name (relaxSt st p m) args hns]
  rw [hfn]
  exact finishMeteredCall_relax extra name st args _ p m fun vals st2 h => by
    obtain ⟨h1, h2⟩ := hkeep st args vals st2 h
    exact ⟨h1 ▸ hp, h2 ▸ hm⟩

end NearLogic
