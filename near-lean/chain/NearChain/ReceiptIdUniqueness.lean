import NearChain.IdentifierBounds
import NearRuntime.BlockFreshReceiptIds

namespace Near
open Wasm.Near

/-- Inter-block pending envelopes have distinct identities. -/
def Snapshot.PendingIdsUnique (s : Snapshot) : Prop := (s.pending.map (·.receiptId)).Nodup

/-- Deferred ids are below the old frontier and new outgoing ids are at or
above it. This allocation premise is necessary when a schedule retains work. -/
theorem step_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (s next : Snapshot) (b : Block)
    (result : ApplyResult) (hs : step cfg decoder s b = .ok (next, result))
    (h : s.PendingIdsUnique) (hbound : ReceiptList.IdsBelow s.state.nextId s.pending) : next.PendingIdsUnique := by
  cases hr : b.receipts.resolve s.pending with
  | error error => simp [step, hr] at hs
  | ok pair =>
    obtain ⟨incoming, deferred⟩ := pair
    have hp := ReceiptSchedule.resolve_perm s.pending b.receipts incoming deferred hr
    have hn : ((incoming ++ deferred).map (·.receiptId)).Nodup := (hp.map (fun receipt : Receipt => receipt.receiptId)).nodup_iff.mpr h
    have hd : (deferred.map (·.receiptId)).Nodup := (List.nodup_append.mp (by simpa only [List.map_append] using hn)).2.1
    simp only [step, hr] at hs
    split at hs
    · cases hs; exact h
    · cases hs
      have hf := apply_freshIds cfg b.ap decoder s.state b.txs incoming
      rw [Snapshot.PendingIdsUnique, List.map_append, List.nodup_append]
      refine ⟨hd, hf.unique, ?_⟩
      intro old hold fresh hnew he
      obtain ⟨receipt, hm, hid⟩ := List.mem_map.mp hold
      obtain ⟨minted, hminted, hmid⟩ := List.mem_map.mp hnew
      have hlow := (hf.bounds minted hminted).1
      have hupp := hbound receipt (hp.mem_iff.mp (List.mem_append_right _ hm)) receipt.receiptId (by simp [Receipt.liveIds])
      rw [hid] at hupp
      rw [hmid, ← he] at hlow
      exact Nat.not_le_of_lt hupp hlow

theorem Reachable.pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hgenesis : genesis.PendingIdsUnique) (hbounds : genesis.IdentifierBounds)
    (h : Reachable cfg decoder genesis s) : s.PendingIdsUnique := by
  induction h with
  | refl => exact hgenesis
  | step b result hs _ reach ih =>
    exact step_pendingIdsUnique cfg decoder _ _ b result hs ih
      (Reachable.identifier_bounds cfg decoder genesis _ hbounds reach).2

theorem settle_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) (h : s.PendingIdsUnique) (hbounds : s.IdentifierBounds) :
    (settle cfg decoder ap s fuel).snapshot.PendingIdsUnique := by
  have hp := settle_snapshot_invariant cfg decoder
    (fun next => next.IdentifierBounds ∧ next.PendingIdsUnique) (fun before next b result hs hb =>
      ⟨step_identifier_bounds cfg decoder before next b result hs hb.1,
        step_pendingIdsUnique cfg decoder before next b result hs hb.2 hb.1.2⟩) ap s fuel ⟨hbounds, h⟩
  exact hp.2

theorem runIsolated_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) (h : s.PendingIdsUnique) (hbounds : s.IdentifierBounds) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.PendingIdsUnique := by
  have hp := runIsolated_snapshot_invariant cfg decoder
    (fun next => next.IdentifierBounds ∧ next.PendingIdsUnique) (fun before next b result hs hb =>
      ⟨step_identifier_bounds cfg decoder before next b result hs hb.1,
        step_pendingIdsUnique cfg decoder before next b result hs hb.2 hb.1.2⟩) ap s txs fuel ⟨hbounds, h⟩
  exact hp.2

end Near
