import NearChain.IdentifierBounds

namespace Near
open Wasm.Near

/-- Inter-block pending envelopes have distinct identities. This says nothing
about cross-queue ownership with delayed and postponed receipts. -/
def Snapshot.PendingIdsUnique (s : Snapshot) : Prop := (s.pending.map (·.receiptId)).Nodup

/-- Retained old envelopes must lie below the allocation frontier, so they
cannot collide with the newly allocated outgoing identities. -/
theorem step_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block)
    (hbound : s.IdentifierBounds) (h : s.PendingIdsUnique) : (step cfg decoder s b).1.PendingIdsUnique := by
  let selected := s.pending.filter (fun receipt => b.deliver receipt.receiptId)
  let held := s.pending.filter (fun receipt => !b.deliver receipt.receiptId)
  have hf := apply_freshIds cfg b.ap decoder s.state b.txs selected
  have hheld : (held.map (·.receiptId)).Nodup :=
    List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h
  unfold step
  simp only [List.partition_eq_filter_filter]
  split
  · exact h
  · change ((held ++ (apply cfg b.ap decoder s.state b.txs selected).outgoing).map (·.receiptId)).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨hheld, hf.unique, ?_⟩
    intro first hfirst last hlast he
    obtain ⟨r, hr, hri⟩ := List.mem_map.mp hfirst
    obtain ⟨t, ht, hti⟩ := List.mem_map.mp hlast
    have oldBound := hbound.2 r (List.mem_filter.mp hr).1 r.receiptId (by simp [Receipt.liveIds])
    have newBound := (hf.bounds t ht).1
    rw [hri] at oldBound
    rw [hti, ← he] at newBound
    exact Nat.not_le_of_lt oldBound newBound

theorem Reachable.pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hbound : genesis.IdentifierBounds) (hgenesis : genesis.PendingIdsUnique)
    (h : Reachable cfg decoder genesis s) : s.PendingIdsUnique := by
  induction h with
  | refl => exact hgenesis
  | step b _ previous ih =>
    exact step_pendingIdsUnique cfg decoder _ b (Reachable.identifier_bounds cfg decoder genesis _ hbound previous) ih

theorem settle_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) (hbound : s.IdentifierBounds) (h : s.PendingIdsUnique) :
    (settle cfg decoder ap s fuel).snapshot.PendingIdsUnique := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    unfold settle
    split
    · exact h
    · dsimp only
      have hs := step_pendingIdsUnique cfg decoder s { ap, txs := [] } hbound h
      have hb := step_identifier_bounds cfg decoder s { ap, txs := [] } hbound
      split
      · exact hs
      · exact ih _ hb hs

theorem runIsolated_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) (hbound : s.IdentifierBounds) (h : s.PendingIdsUnique) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.PendingIdsUnique := by
  unfold runIsolated
  dsimp only
  have hs := step_pendingIdsUnique cfg decoder s { ap, txs } hbound h
  have hb := step_identifier_bounds cfg decoder s { ap, txs } hbound
  split
  · exact hs
  · exact settle_pendingIdsUnique cfg decoder ap _ fuel hb hs

end Near
