import NearLogic.Hosts.Mono
import NearLogic.Hosts.StorageRelax

/-!
# Failed charges keep the logs and the execution issue

The relaxation lemmas with their gas case strengthened: a charge that fails
under the lower limits traps on a store whose execution issue is the
call's input's, and whose logs are a prefix of what the call returns under
raised limits. With it, the logs of a run that runs out of gas are a
prefix of the logs of the same run with enough gas.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A failed charge of a call from `input`, against the raised call's result `rr`. -/
def GasTrapR (issue : Option ExecutionIssue) (r rr : HostResult NearState) : Prop :=
  ∃ st e, r = trapWith st e ∧ isGasError e ∧ st.host.lastExecutionIssue = issue ∧
    st.host.logs <+: (resHost rr).logs

theorem resHost_relax (r : HostResult NearState) (p m : Nat) : resHost (r.relax p m) = relax (resHost r) p m := by
  cases r <;> rfl

theorem finishMeteredCall_relaxL (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (r : HostResult NearState) (p m : Nat) (issue : Option ExecutionIssue)
    (hlim : ∀ vals st2, r = .Return vals st2 → st2.host.gas.prepaid ≤ p ∧ st2.host.gas.maxBurnt ≤ m)
    (hiss : ∀ vals st2, r = .Return vals st2 → st2.host.lastExecutionIssue = issue) :
    GasTrapR issue (finishMeteredCall extra name before args r)
        (finishMeteredCall extra name (relaxSt before p m) args (r.relax p m)) ∨
      finishMeteredCall extra name (relaxSt before p m) args (r.relax p m) =
        (finishMeteredCall extra name before args r).relax p m := by
  have hlogs := (finishMeteredCall_mono extra name (relaxSt before p m) args (r.relax p m)).1
  rw [resHost_relax] at hlogs
  cases r with
  | Trap st2 msg => right; rfl
  | Return vals st2 =>
    obtain ⟨hp, hm⟩ := hlim vals st2 rfl
    have hi2 := hiss vals st2 rfl
    simp only [resHost, relax_logs] at hlogs
    revert hlogs
    simp only [finishMeteredCall, HostResult.relax]
    rw [chargesAfter_relax, show (relaxSt st2 p m).host = relax st2.host p m from rfl]
    intro hlogs
    cases hac : applyCharges st2.host (chargesAfter name before st2 args) with
    | mk ns err =>
      have hl := applyCharges_logs st2.host (chargesAfter name before st2 args)
      have hi := applyCharges_issue st2.host (chargesAfter name before st2 args)
      rw [hac] at hl hi
      cases err with
      | some e =>
        left
        refine ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac]), by simp only; rw [hi, hi2], ?_⟩
        exact pre_eq (hlogs.trans hl.symm)
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
theorem prepareStorageCall_logs (name : String) (st : HostStore NearState) (args : List Value) :
    (prepareStorageCall name st args).1.host.logs = st.host.logs ∧
      (prepareStorageCall name st args).1.host.lastExecutionIssue = st.host.lastExecutionIssue := ⟨rfl, rfl⟩

/-- The call after the charges only grows the logs. -/
theorem invokeStorageCall_mono (extra : Nat) (name : String) (fn : NearHostFn NearState) (hfn : FnMono fn)
    (st : HostStore NearState) (args : List Value) :
    st.host.logs <+: (resHost (invokeStorageCall extra name fn st args)).logs := by
  have hpl := (prepareStorageCall_logs name st args).1
  simp only [invokeStorageCall]
  generalize prepareStorageCall name st args = q at hpl
  obtain ⟨after, perr⟩ := q
  simp only at hpl
  cases perr with
  | some pe => cases pe <;> exact pre_eq hpl
  | none =>
    simp only
    rw [(finishMeteredCall_mono extra name after args (fn.invoke after args)).1, ← hpl]
    exact (hfn after args).1

/-- The call after the charges, under raised limits, with its failed charges' logs and issue. -/
def InvokeRelaxL (extra : Nat) (name : String) (fn : NearHostFn NearState) : Prop :=
  ∀ (st : HostStore NearState) (args : List Value) (p m : Nat),
    st.host.gas.prepaid ≤ p → st.host.gas.maxBurnt ≤ m →
    GasTrapR st.host.lastExecutionIssue (invokeStorageCall extra name fn st args)
        (invokeStorageCall extra name fn (relaxSt st p m) args) ∨
      invokeStorageCall extra name fn (relaxSt st p m) args = (invokeStorageCall extra name fn st args).relax p m

theorem invokeRelaxL_plain (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hns : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains name = false)
    (hfn : ∀ st args p m, fn.invoke (relaxSt st p m) args = (fn.invoke st args).relax p m)
    (hkeep : ∀ st args vals st2, fn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt)
    (hmono : FnMono fn) : InvokeRelaxL extra name fn := by
  intro st args p m hp hm
  simp only [invokeStorageCall, prepareStorageCall_other name st args hns,
    prepareStorageCall_other name (relaxSt st p m) args hns]
  rw [hfn]
  exact finishMeteredCall_relaxL extra name st args _ p m st.host.lastExecutionIssue
    (fun vals st2 h => by
      obtain ⟨h1, h2⟩ := hkeep st args vals st2 h
      exact ⟨h1 ▸ hp, h2 ▸ hm⟩)
    (fun vals st2 h => (hmono st args).2 vals st2 h)

theorem invokeRelaxL_storage (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : ∀ st args p m, fn.invoke (relaxSt st p m) args = (fn.invoke st args).relax p m)
    (hkeep : ∀ st args vals st2, fn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt)
    (hmono : FnMono fn) : InvokeRelaxL extra name fn := by
  intro st args p m hp hm
  have hl := prepareStorageCall_limits name st args
  have hlog := prepareStorageCall_logs name st args
  have hrm := invokeStorageCall_mono extra name fn hmono (relaxSt st p m) args
  rcases prepareStorageCall_relax name st args p m hp hm with ⟨e, he, hg⟩ | hr
  · left
    refine ⟨(prepareStorageCall name st args).1, e, ?_, hg, hlog.2, ?_⟩
    · simp only [invokeStorageCall]
      rw [he]
    · rw [hlog.1]; exact hrm
  · simp only [invokeStorageCall]
    rw [hr]
    generalize prepareStorageCall name st args = r at hl hlog ⊢
    obtain ⟨after, err⟩ := r
    simp only at hl hlog ⊢
    cases err with
    | none =>
      simp only
      rw [hfn]
      exact finishMeteredCall_relaxL extra name after args _ p m st.host.lastExecutionIssue
        (fun vals st2 h => by
          obtain ⟨h1, h2⟩ := hkeep after args vals st2 h
          exact ⟨by rw [h1, hl.1]; exact hp, by rw [h2, hl.2]; exact hm⟩)
        (fun vals st2 h => ((hmono after args).2 vals st2 h).trans hlog.2)
    | some err =>
      right
      cases err <;> rfl

/-- **The metered wrapper under raised limits, with logs**: a failed charge
keeps the input's execution issue and logs no more than the raised call. -/
theorem metered_relaxL (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hcb : ∀ st args p m, chargesBefore name (relaxSt st p m) args = chargesBefore name st args)
    (hpre : ∀ st args p m, preInvokeError name (relaxSt st p m) args = preInvokeError name st args)
    (hinv : InvokeRelaxL extra name fn) (hmono : FnMono fn)
    (st : HostStore NearState) (args : List Value) (p m : Nat)
    (hp : st.host.gas.prepaid ≤ p) (hm : st.host.gas.maxBurnt ≤ m) :
    GasTrapR st.host.lastExecutionIssue ((metered extra name fn).invoke st args)
        ((metered extra name fn).invoke (relaxSt st p m) args) ∨
      (metered extra name fn).invoke (relaxSt st p m) args = ((metered extra name fn).invoke st args).relax p m := by
  have hrm := (metered_mono extra name fn hmono (relaxSt st p m) args).1
  revert hrm
  have hctx : (relaxSt st p m).host.context = st.host.context := rfl
  simp only [metered]
  rw [hctx]
  intro hrm
  by_cases hdep : deprecatedRuntimeHost name = true
  · right; simp only [hdep, ite_true]; rfl
  simp only [hdep, Bool.false_eq_true, ite_false] at hrm ⊢
  by_cases hview : (st.host.context.isView && viewRestrictedHost name) = true
  · simp only [hview, ite_true] at hrm ⊢
    generalize (([.ext "base"] ++ (if name == "promise_return" then [.ext "promise_return"] else [])) :
      List Charge) = cs at hrm ⊢
    rw [show (relaxSt st p m).host = relax st.host p m from rfl] at hrm ⊢
    have hl := applyCharges_logs st.host cs
    have hi := applyCharges_issue st.host cs
    cases hac : applyCharges st.host cs with
    | mk ns err =>
      rw [hac] at hl hi
      cases err with
      | some e =>
        left
        exact ⟨{ st with host := ns }, e, rfl, applyCharges_error _ _ (by rw [hac]), hi,
          (pre_eq hl.symm).trans hrm⟩
      | none =>
        right
        have hrel := applyCharges_relax st.host cs p m hp hm (by rw [hac])
        rw [hac] at hrel
        rw [hrel]
        rfl
  simp only [hview, Bool.false_eq_true, ite_false] at hrm ⊢
  rw [hcb, show (relaxSt st p m).host = relax st.host p m from rfl] at hrm ⊢
  have hl := applyCharges_logs st.host (chargesBefore name st args)
  have hi := applyCharges_issue st.host (chargesBefore name st args)
  cases hac : applyCharges st.host (chargesBefore name st args) with
  | mk ns err =>
    rw [hac] at hl hi
    have hlims := applyCharges_gas_limits st.host (chargesBefore name st args)
    rw [hac] at hlims
    cases err with
    | some e =>
      left
      exact ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac]), hi, (pre_eq hl.symm).trans hrm⟩
    | none =>
      have hrel := applyCharges_relax st.host (chargesBefore name st args) p m hp hm (by rw [hac])
      rw [hac] at hrel
      rw [hrel] at hrm ⊢
      let st1 : HostStore NearState :=
        { st with host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have hrm' : st.host.logs <+: (resHost (match preInvokeError name (relaxSt st1 p m) args with
          | some error => trapWith (relaxSt st1 p m) error
          | none => invokeStorageCall extra name fn (relaxSt st1 p m) args)).logs := hrm
      have htail : GasTrapR st.host.lastExecutionIssue (match preInvokeError name st1 args with
          | some error => trapWith st1 error
          | none => invokeStorageCall extra name fn st1 args)
          (match preInvokeError name (relaxSt st1 p m) args with
            | some error => trapWith (relaxSt st1 p m) error
            | none => invokeStorageCall extra name fn (relaxSt st1 p m) args) ∨
          (match preInvokeError name (relaxSt st1 p m) args with
            | some error => trapWith (relaxSt st1 p m) error
            | none => invokeStorageCall extra name fn (relaxSt st1 p m) args) =
          (match preInvokeError name st1 args with
            | some error => trapWith st1 error
            | none => invokeStorageCall extra name fn st1 args).relax p m := by
        rw [hpre] at hrm' ⊢
        cases preInvokeError name st1 args with
        | some e => right; rfl
        | none =>
          have hst1 : st1.host.lastExecutionIssue = st.host.lastExecutionIssue := hi
          rw [← hst1]
          exact hinv st1 args p m (by show ns.gas.prepaid ≤ p; rw [hlims.1]; exact hp)
            (by show ns.gas.maxBurnt ≤ m; rw [hlims.2]; exact hm)
      exact htail

end NearLogic
