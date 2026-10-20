import NearChain.AllocatorMonotonicity

namespace Near
open Wasm.Near

/-- The routing state and all inter-block pending receipts use allocated ids.
This numeric bound does not assert ownership, uniqueness or graph validity. -/
def Snapshot.IdentifierBounds (s : Snapshot) : Prop :=
  s.state.IdsBelowNext ∧ ReceiptList.IdsBelow s.state.nextId s.pending

theorem step_identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block)
    (h : s.IdentifierBounds) : (step cfg decoder s b).1.IdentifierBounds := by
  unfold step
  dsimp only
  split
  · exact h
  · exact apply_identifier_bounds cfg b.ap decoder s.state b.txs s.pending h.1 h.2

/-- Bounds for every referenced id survive arbitrary supported block sequences. -/
theorem Reachable.identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hgenesis : genesis.IdentifierBounds) (h : Reachable cfg decoder genesis s) : s.IdentifierBounds := by
  induction h with
  | refl => exact hgenesis
  | step b _ _ ih => exact step_identifier_bounds cfg decoder _ b ih

theorem settle_identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) (h : s.IdentifierBounds) :
    (settle cfg decoder ap s fuel).snapshot.IdentifierBounds := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    unfold settle
    split
    · exact h
    · dsimp only
      have hs := step_identifier_bounds cfg decoder s { ap, txs := [] } h
      split
      · exact hs
      · exact ih _ hs

theorem runIsolated_identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) (h : s.IdentifierBounds) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.IdentifierBounds := by
  unfold runIsolated
  dsimp only
  have hs := step_identifier_bounds cfg decoder s { ap, txs } h
  split
  · exact hs
  · exact settle_identifier_bounds cfg decoder ap _ fuel hs

/-- The allocator frontier cannot coincide with any currently live routing or
pending reference. Duplicate ids already below that frontier are not excluded. -/
theorem Snapshot.IdentifierBounds.nextId_fresh (s : Snapshot) (h : s.IdentifierBounds) :
    s.state.nextId ∉ s.state.liveIds ∧ ∀ receipt ∈ s.pending, s.state.nextId ∉ receipt.liveIds := by
  refine ⟨h.1.fresh, ?_⟩
  intro receipt hm hid
  exact Nat.lt_irrefl _ (h.2 receipt hm _ hid)

end Near
