import NearChain.ReceiptIdUniqueness
import NearRuntime.PostponedOwnership
import NearRuntime.BlockStatePreservation

namespace Near
open Wasm.Near

theorem step_postponedIdsMatch (cfg : RuntimeConfig) (decoder : CodeTable) (s next : Snapshot) (b : Block)
    (result : ApplyResult) (hs : step cfg decoder s b = .ok (next, result))
    (h : s.state.PostponedIdsMatch) : next.state.PostponedIdsMatch :=
  step_state_invariant cfg decoder ChainState.PostponedIdsMatch
    (fun ap st txs incoming h => apply_postponedIdsMatch cfg ap decoder st txs incoming h) s next b result hs h

/-- State predicates propagate through every accepted public step. -/
theorem Reachable.state_invariant (cfg : RuntimeConfig) (decoder : CodeTable) (P : ChainState → Prop)
    (hstep : ∀ s next b result, Near.step cfg decoder s b = .ok (next, result) → P s.state → P next.state)
    (genesis s : Snapshot) (hgenesis : P genesis.state) (h : Reachable cfg decoder genesis s) : P s.state := by
  induction h with
  | refl => exact hgenesis
  | step b result hs _ _ ih => exact hstep _ _ b result hs ih

/-- Stored receipt/key agreement is inherited from genesis. -/
theorem Reachable.postponedIdsMatch (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hgenesis : genesis.state.PostponedIdsMatch) (h : Reachable cfg decoder genesis s) :
    s.state.PostponedIdsMatch :=
  Reachable.state_invariant cfg decoder ChainState.PostponedIdsMatch
    (step_postponedIdsMatch cfg decoder) genesis s hgenesis h

end Near
