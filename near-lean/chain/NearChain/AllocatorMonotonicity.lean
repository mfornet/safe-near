import NearChain.ReservedActorInvariant
import NearRuntime.BlockAllocatorMonotonicity

namespace Near
open Wasm.Near

/-- Every accepted schedule retains the allocator frontier, including issues. -/
theorem step_nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (s next : Snapshot) (b : Block)
    (result : ApplyResult) (hs : step cfg decoder s b = .ok (next, result)) :
    s.state.nextId ≤ next.state.nextId := by
  apply step_state_invariant cfg decoder (fun st => s.state.nextId ≤ st.nextId) _ s next b result hs (Nat.le_refl _)
  intro ap st txs incoming h
  exact h.trans (apply_nextId_mono cfg ap decoder st txs incoming)

theorem Reachable.nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (h : Reachable cfg decoder genesis s) : genesis.state.nextId ≤ s.state.nextId := by
  induction h with
  | refl => exact Nat.le_refl _
  | step b result hs _ _ ih => exact ih.trans (step_nextId_mono cfg decoder _ _ b result hs)

/-- Bounded settlement cannot rewind its initial allocator frontier. -/
theorem settle_nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) : s.state.nextId ≤ (settle cfg decoder ap s fuel).snapshot.state.nextId := by
  apply settle_snapshot_invariant cfg decoder (fun next => s.state.nextId ≤ next.state.nextId) _ ap s fuel (Nat.le_refl _)
  intro before next b result hs h
  exact h.trans (step_nextId_mono cfg decoder before next b result hs)

theorem runIsolated_nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) :
    s.state.nextId ≤ (runIsolated cfg decoder ap s txs fuel).snapshot.state.nextId := by
  apply runIsolated_snapshot_invariant cfg decoder (fun next => s.state.nextId ≤ next.state.nextId) _ ap s txs fuel (Nat.le_refl _)
  intro before next b result hs h
  exact h.trans (step_nextId_mono cfg decoder before next b result hs)

/-- Previously allocated ids remain below every reachable frontier. -/
theorem Reachable.retains_id_bound (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (h : Reachable cfg decoder genesis s) (id : Nat) (hid : id < genesis.state.nextId) : id < s.state.nextId :=
  hid.trans_le (Reachable.nextId_mono cfg decoder genesis s h)

end Near
