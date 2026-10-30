import NearLogic.Hosts.RelaxFns

/-!
# Host functions only grow the logs

`FnMono fn`: a functional host only appends to the logs, and records an
execution issue only when it traps. The metered wrapper keeps this
(`metered_mono`), so along a run the logs only grow and a running machine
has no execution issue: what the out-of-gas case of `Refines` needs.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- The host of a host result. -/
def resHost : HostResult NearState → NearState
  | .Return _ st => st.host
  | .Trap st _ => st.host

/-- The host only appends to the logs, and keeps its execution issue when it returns. -/
def FnMono (fn : NearHostFn NearState) : Prop :=
  ∀ (st : HostStore NearState) (args : List Value),
    st.host.logs <+: (resHost (fn.invoke st args)).logs ∧
      ∀ vals st', fn.invoke st args = .Return vals st' → st'.host.lastExecutionIssue = st.host.lastExecutionIssue

theorem applyCharges_logs (ns : NearState) (cs : List Charge) : (applyCharges ns cs).1.logs = ns.logs :=
  erase_field (applyCharges_erase ns cs) NearState.logs fun _ => rfl

theorem applyCharges_issue (ns : NearState) (cs : List Charge) :
    (applyCharges ns cs).1.lastExecutionIssue = ns.lastExecutionIssue :=
  erase_field (applyCharges_erase ns cs) NearState.lastExecutionIssue fun _ => rfl

theorem pre_eq {α : Type} {l l' : List α} (h : l' = l) : l <+: l' := h ▸ List.prefix_refl l

theorem trapWith_mono (st : HostStore NearState) (e : HostError) (l : List (List UInt8))
    {P : List Value → HostStore NearState → Prop} (h : l <+: st.host.logs) :
    l <+: (resHost (trapWith st e)).logs ∧ ∀ vals st', trapWith st e = .Return vals st' → P vals st' :=
  ⟨h, fun _ _ h => by cases h⟩

theorem deductDeposit_logs (name : String) (before after : HostStore NearState) (args : List Value) :
    (deductDeposit name before after args).1.host.logs = after.host.logs ∧
      (deductDeposit name before after args).1.host.lastExecutionIssue = after.host.lastExecutionIssue := by
  unfold deductDeposit
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · unfold deductPromiseDeposit; dsimp only; split <;> (try split) <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem updateStorageUsage_logs (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) :
    (updateStorageUsage extra name before after args).host.logs = after.host.logs ∧
      (updateStorageUsage extra name before after args).host.lastExecutionIssue = after.host.lastExecutionIssue := by
  unfold updateStorageUsage
  dsimp only
  split <;> (try split) <;> exact ⟨rfl, rfl⟩

/-- What `finishMeteredCall` does to the logs and the issue: nothing. -/
theorem finishMeteredCall_mono (extra : Nat) (name : String) (before : HostStore NearState) (args : List Value)
    (r : HostResult NearState) :
    (resHost (finishMeteredCall extra name before args r)).logs = (resHost r).logs ∧
      ∀ vals st', finishMeteredCall extra name before args r = .Return vals st' →
        ∃ st2, r = .Return vals st2 ∧ st'.host.lastExecutionIssue = st2.host.lastExecutionIssue := by
  cases r with
  | Trap st msg => exact ⟨rfl, fun _ _ h => by cases h⟩
  | Return vals st2 =>
    simp only [finishMeteredCall]
    have hl := applyCharges_logs st2.host (chargesAfter name before st2 args)
    have hi := applyCharges_issue st2.host (chargesAfter name before st2 args)
    generalize applyCharges st2.host (chargesAfter name before st2 args) = a at hl hi
    obtain ⟨ns, err⟩ := a
    cases err with
    | some e => exact ⟨hl, fun _ _ h => by cases h⟩
    | none =>
      simp only
      have hd := deductDeposit_logs name before { st2 with host := ns } args
      generalize deductDeposit name before { st2 with host := ns } args = d at hd
      obtain ⟨st4, e4⟩ := d
      cases e4 with
      | some e => exact ⟨hd.1.trans hl, fun _ _ h => by cases h⟩
      | none =>
        simp only
        cases actionMethodEncodingError name before args with
        | some e => exact ⟨hd.1.trans hl, fun _ _ h => by cases h⟩
        | none =>
          have hu := updateStorageUsage_logs extra name before st4 args
          refine ⟨hu.1.trans (hd.1.trans hl), fun vals' st' h => ?_⟩
          cases h
          exact ⟨st2, rfl, hu.2.trans (hd.2.trans hi)⟩

/-- **The metered wrapper keeps `FnMono`.** -/
theorem metered_mono (extra : Nat) (name : String) (fn : NearHostFn NearState) (hfn : FnMono fn) :
    FnMono (metered extra name fn) := by
  intro st args
  simp only [metered]
  split
  · exact trapWith_mono _ _ _ (List.prefix_refl _)
  split
  · generalize (([.ext "base"] ++ (if name == "promise_return" then [.ext "promise_return"] else [])) :
      List Charge) = cs
    have hl' := applyCharges_logs st.host cs
    generalize applyCharges st.host cs = a at hl'
    obtain ⟨ns, e⟩ := a
    simp only at hl' ⊢
    (refine trapWith_mono _ _ st.host.logs ?_; exact pre_eq hl')
  have hl := applyCharges_logs st.host (chargesBefore name st args)
  have hi := applyCharges_issue st.host (chargesBefore name st args)
  generalize applyCharges st.host (chargesBefore name st args) = a at hl hi
  obtain ⟨ns, err⟩ := a
  simp only at hl hi
  cases err with
  | some e => simp only; (refine trapWith_mono _ _ st.host.logs ?_; exact pre_eq hl)
  | none =>
    simp only
    split
    · (refine trapWith_mono _ _ st.host.logs ?_; exact pre_eq hl)
    · simp only [invokeStorageCall]
      have hpl : (prepareStorageCall name { st with host := { ns with context := { ns.context with
          usedGas := UInt64.ofNat ns.gas.used } } } args).1.host.logs = st.host.logs := by
        rw [← hl]; rfl
      have hpi : (prepareStorageCall name { st with host := { ns with context := { ns.context with
          usedGas := UInt64.ofNat ns.gas.used } } } args).1.host.lastExecutionIssue = st.host.lastExecutionIssue := by
        rw [← hi]; rfl
      generalize prepareStorageCall name _ args = q at hpl hpi
      obtain ⟨after, perr⟩ := q
      simp only at hpl hpi
      cases perr with
      | some pe =>
        cases pe <;> first
          | (refine trapWith_mono _ _ st.host.logs ?_; exact pre_eq hpl)
          | exact ⟨pre_eq hpl, fun _ _ h => by cases h⟩
      | none =>
        simp only
        obtain ⟨hfl, hfi⟩ := finishMeteredCall_mono extra name after args (fn.invoke after args)
        obtain ⟨hml, hmi⟩ := hfn after args
        refine ⟨by rw [hfl, ← hpl]; exact hml, fun vals st' h => ?_⟩
        obtain ⟨st2, h2, hs⟩ := hfi vals st' h
        rw [hs, hmi vals st2 h2, hpi]

end NearLogic
