import NearChain.ReceiptIdUniqueness

namespace Near
open Wasm.Near

theorem step_postponedIdsMatch (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block)
    (h : s.state.PostponedIdsMatch) : (step cfg decoder s b).1.state.PostponedIdsMatch := by
  unfold step
  simp only [List.partition_eq_filter_filter]
  split
  · exact h
  · exact apply_postponedIdsMatch cfg b.ap decoder s.state b.txs (s.pending.filter (fun receipt => b.deliver receipt.receiptId)) h

/-- A state-predicate induction rule over the public reachability relation. -/
theorem Reachable.state_invariant (cfg : RuntimeConfig) (decoder : CodeTable) (P : ChainState → Prop)
    (hstep : ∀ (s : Snapshot) (b : Block), P s.state → P (Near.step cfg decoder s b).1.state)
    (genesis s : Snapshot) (hgenesis : P genesis.state) (h : Reachable cfg decoder genesis s) : P s.state := by
  induction h with
  | refl => exact hgenesis
  | step b _ _ ih => exact hstep _ b ih

/-- Identity agreement is inherited from genesis, so later queue-admission
proofs can use it without assuming it independently for every block. -/
theorem Reachable.postponedIdsMatch (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hgenesis : genesis.state.PostponedIdsMatch) (h : Reachable cfg decoder genesis s) :
    s.state.PostponedIdsMatch :=
  Reachable.state_invariant cfg decoder ChainState.PostponedIdsMatch
    (step_postponedIdsMatch cfg decoder) genesis s hgenesis h

end Near
