import NearChain.ReservedActorInvariant

namespace Near
open Wasm.Near

/-- A block step retains the allocator frontier on every public result. -/
theorem step_nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block) :
    s.state.nextId ≤ (step cfg decoder s b).1.state.nextId := by
  unfold step
  dsimp only
  split
  · exact Nat.le_refl _
  · exact apply_nextId_mono cfg b.ap decoder s.state b.txs s.pending

theorem Reachable.nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (h : Reachable cfg decoder genesis s) : genesis.state.nextId ≤ s.state.nextId := by
  induction h with
  | refl => exact Nat.le_refl _
  | step b _ _ ih => exact ih.trans (step_nextId_mono cfg decoder _ b)

/-- A bounded run cannot rewind the initial frontier for any stop reason. -/
theorem settle_nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) : s.state.nextId ≤ (settle cfg decoder ap s fuel).snapshot.state.nextId := by
  induction fuel generalizing s with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    unfold settle
    split
    · exact Nat.le_refl _
    · dsimp only
      have hs := step_nextId_mono cfg decoder s { ap, txs := [] }
      split
      · exact hs
      · exact hs.trans (ih _)

theorem runIsolated_nextId_mono (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) :
    s.state.nextId ≤ (runIsolated cfg decoder ap s txs fuel).snapshot.state.nextId := by
  unfold runIsolated
  dsimp only
  have hs := step_nextId_mono cfg decoder s { ap, txs }
  split
  · exact hs
  · exact hs.trans (settle_nextId_mono cfg decoder ap _ fuel)

/-- A previously allocated reference stays below the counter in every reachable
state. This does not assert ownership or uniqueness of pending receipt ids. -/
theorem Reachable.retains_id_bound (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (h : Reachable cfg decoder genesis s) (id : Nat) (hid : id < genesis.state.nextId) : id < s.state.nextId :=
  hid.trans_le (Reachable.nextId_mono cfg decoder genesis s h)

end Near
