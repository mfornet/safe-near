import NearChain.AllocatorMonotonicity

namespace Near
open Wasm.Near

/-- Routing state and all inter-block pending receipts use allocated ids.
This numeric bound does not assert ownership, uniqueness or graph validity. -/
def Snapshot.IdentifierBounds (s : Snapshot) : Prop :=
  s.state.IdsBelowNext ∧ ReceiptList.IdsBelow s.state.nextId s.pending

theorem step_identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (s next : Snapshot) (b : Block)
    (result : ApplyResult) (hs : step cfg decoder s b = .ok (next, result))
    (h : s.IdentifierBounds) : next.IdentifierBounds := by
  cases hr : b.receipts.resolve s.pending with
  | error error => simp [step, hr] at hs
  | ok pair =>
    obtain ⟨incoming, deferred⟩ := pair
    have hp := ReceiptSchedule.resolve_perm s.pending b.receipts incoming deferred hr
    have hin : ReceiptList.IdsBelow s.state.nextId incoming := by
      intro receipt hm
      exact h.2 receipt (hp.mem_iff.mp (List.mem_append_left _ hm))
    have hdefer : ReceiptList.IdsBelow s.state.nextId deferred := by
      intro receipt hm
      exact h.2 receipt (hp.mem_iff.mp (List.mem_append_right _ hm))
    simp only [step, hr] at hs
    split at hs
    · cases hs; exact h
    · cases hs
      have ha := apply_identifier_bounds cfg b.ap decoder s.state b.txs incoming h.1 hin
      exact ⟨ha.1, (hdefer.mono (apply_nextId_mono cfg b.ap decoder s.state b.txs incoming)).append ha.2⟩

/-- Every reference stays allocated under arbitrary accepted schedules. -/
theorem Reachable.identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hgenesis : genesis.IdentifierBounds) (h : Reachable cfg decoder genesis s) : s.IdentifierBounds := by
  induction h with
  | refl => exact hgenesis
  | step b result hs _ _ ih => exact step_identifier_bounds cfg decoder _ _ b result hs ih

theorem settle_identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) (h : s.IdentifierBounds) :
    (settle cfg decoder ap s fuel).snapshot.IdentifierBounds :=
  settle_snapshot_invariant cfg decoder Snapshot.IdentifierBounds (step_identifier_bounds cfg decoder) ap s fuel h

theorem runIsolated_identifier_bounds (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) (h : s.IdentifierBounds) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.IdentifierBounds :=
  runIsolated_snapshot_invariant cfg decoder Snapshot.IdentifierBounds (step_identifier_bounds cfg decoder) ap s txs fuel h

/-- The allocator frontier cannot coincide with any live routing or pending id. -/
theorem Snapshot.IdentifierBounds.nextId_fresh (s : Snapshot) (h : s.IdentifierBounds) :
    s.state.nextId ∉ s.state.liveIds ∧ ∀ receipt ∈ s.pending, s.state.nextId ∉ receipt.liveIds := by
  refine ⟨h.1.fresh, ?_⟩
  intro receipt hm hid
  exact Nat.lt_irrefl _ (h.2 receipt hm _ hid)

end Near
