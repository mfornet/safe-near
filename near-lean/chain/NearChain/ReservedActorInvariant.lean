import NearChain.Step
import NearRuntime

namespace Near
open Wasm.Near

/-- The reserved synthetic actor cannot become a stored account in a block,
including rejected attempts and gas-limited scheduling. -/
theorem step_systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (s : Snapshot) (b : Block) (h : s.state.SystemAccountAbsent) :
    (step cfg decoder s b).1.state.SystemAccountAbsent := by
  unfold step
  simp only [List.partition_eq_filter_filter]
  split
  · exact h
  · exact apply_systemAbsent cfg b.ap decoder s.state b.txs (s.pending.filter (fun receipt => b.deliver receipt.receiptId)) h

/-- Any reachable chain state preserves genesis absence of the synthetic actor.
No fairness, receipt-shape or successful-contract assumption is required. -/
theorem Reachable.systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (genesis s : Snapshot) (hgenesis : genesis.state.SystemAccountAbsent)
    (hreachable : Reachable cfg decoder genesis s) : s.state.SystemAccountAbsent := by
  induction hreachable with
  | refl => exact hgenesis
  | step b _ _ ih => exact step_systemAbsent cfg decoder _ b ih

/-- Bounded settlement retains the invariant for every stop reason. -/
theorem settle_systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (ap : ApplyState) (s : Snapshot) (fuel : Nat) (h : s.state.SystemAccountAbsent) :
    (settle cfg decoder ap s fuel).snapshot.state.SystemAccountAbsent := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    unfold settle
    split
    · exact h
    · dsimp only
      have hs := step_systemAbsent cfg decoder s { ap, txs := [] } h
      split
      · exact hs
      · exact ih _ hs

/-- An isolated transaction run retains the invariant whether it finishes,
runs out of blocks or encounters an execution issue. -/
theorem runIsolated_systemAbsent (cfg : RuntimeConfig) (decoder : CodeTable)
    (ap : ApplyState) (s : Snapshot) (txs : List Transaction) (fuel : Nat)
    (h : s.state.SystemAccountAbsent) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.state.SystemAccountAbsent := by
  unfold runIsolated
  dsimp only
  have hs := step_systemAbsent cfg decoder s { ap, txs } h
  split
  · exact hs
  · exact settle_systemAbsent cfg decoder ap _ fuel hs

end Near
