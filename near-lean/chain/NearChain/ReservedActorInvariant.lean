import NearChain.Step

namespace Near
open Wasm.Near

/-- A successful public step preserves any state predicate preserved by runtime
apply. Invalid schedules expose no next snapshot; issues retain the old one. -/
theorem step_state_invariant (cfg : RuntimeConfig) (decoder : CodeTable) (P : ChainState → Prop)
    (happly : ∀ ap st txs incoming, P st → P (apply cfg ap decoder st txs incoming).state)
    (s next : Snapshot) (b : Block) (result : ApplyResult)
    (hs : step cfg decoder s b = .ok (next, result)) (h : P s.state) : P next.state := by
  cases hr : b.receipts.resolve s.pending with
  | error error => simp [step, hr] at hs
  | ok pair =>
    obtain ⟨incoming, deferred⟩ := pair
    simp only [step, hr] at hs
    split at hs
    · cases hs; exact h
    · cases hs; exact happly _ _ _ _ h

/-- Snapshot invariants propagate through every bounded settlement stop reason. -/
theorem settle_snapshot_invariant (cfg : RuntimeConfig) (decoder : CodeTable) (P : Snapshot → Prop)
    (hstep : ∀ s next b result, step cfg decoder s b = .ok (next, result) → P s → P next)
    (ap : ApplyState) (s : Snapshot) (fuel : Nat) (h : P s) :
    P (settle cfg decoder ap s fuel).snapshot := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    by_cases hquiet : s.quiescent = true
    · simpa only [settle, hquiet, ite_true, RunResult.finish] using h
    · cases hr : step cfg decoder s { ap, txs := [] } with
      | error error => simpa only [settle, hquiet, Bool.false_eq_true, ite_false, hr] using h
      | ok pair =>
        obtain ⟨next, result⟩ := pair
        have hn := hstep s next _ result hr h
        cases hi : result.issue with
        | some issue => simpa only [settle, hquiet, Bool.false_eq_true, ite_false, hr, hi] using hn
        | none => simpa only [settle, hquiet, Bool.false_eq_true, ite_false, hr, hi] using ih next hn

theorem runIsolated_snapshot_invariant (cfg : RuntimeConfig) (decoder : CodeTable) (P : Snapshot → Prop)
    (hstep : ∀ s next b result, step cfg decoder s b = .ok (next, result) → P s → P next)
    (ap : ApplyState) (s : Snapshot) (txs : List Transaction) (fuel : Nat) (h : P s) :
    P (runIsolated cfg decoder ap s txs fuel).snapshot := by
  cases hr : step cfg decoder s { ap, txs } with
  | error error => simpa only [runIsolated, hr] using h
  | ok pair =>
    obtain ⟨next, result⟩ := pair
    have hn := hstep s next _ result hr h
    cases hi : result.issue with
    | some issue => simpa only [runIsolated, hr, hi] using hn
    | none =>
      simpa only [runIsolated, hr, hi] using settle_snapshot_invariant cfg decoder P hstep ap next fuel hn

/-- The reserved synthetic actor remains absent for every accepted schedule. -/
theorem step_systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (s next : Snapshot) (b : Block) (result : ApplyResult)
    (hs : step cfg decoder s b = .ok (next, result)) (h : s.state.SystemAccountAbsent) :
    next.state.SystemAccountAbsent :=
  step_state_invariant cfg decoder ChainState.SystemAccountAbsent (fun ap st txs incoming h => apply_systemAbsent cfg ap decoder st txs incoming h)
    s next b result hs h

/-- Every reachable state inherits genesis absence of the synthetic actor. -/
theorem Reachable.systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (genesis s : Snapshot) (hgenesis : genesis.state.SystemAccountAbsent)
    (hreachable : Reachable cfg decoder genesis s) : s.state.SystemAccountAbsent := by
  induction hreachable with
  | refl => exact hgenesis
  | step b result hs _ _ ih => exact step_systemAbsent cfg decoder _ _ b result hs ih

theorem settle_systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (ap : ApplyState) (s : Snapshot) (fuel : Nat) (h : s.state.SystemAccountAbsent) :
    (settle cfg decoder ap s fuel).snapshot.state.SystemAccountAbsent :=
  settle_snapshot_invariant cfg decoder (fun s => s.state.SystemAccountAbsent)
    (fun s next b result hs h => step_systemAbsent cfg decoder s next b result hs h) ap s fuel h

theorem runIsolated_systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (ap : ApplyState) (s : Snapshot) (txs : List Transaction) (fuel : Nat)
    (h : s.state.SystemAccountAbsent) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.state.SystemAccountAbsent :=
  runIsolated_snapshot_invariant cfg decoder (fun s => s.state.SystemAccountAbsent)
    (fun s next b result hs h => step_systemAbsent cfg decoder s next b result hs h) ap s txs fuel h

end Near
