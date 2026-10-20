import NearChain.IdentifierBounds

namespace Near
open Wasm.Near

/-- Inter-block pending envelopes have distinct identities. This says nothing
about cross-queue ownership with delayed and postponed receipts. -/
def Snapshot.PendingIdsUnique (s : Snapshot) : Prop := (s.pending.map (·.receiptId)).Nodup

theorem step_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block)
    (h : s.PendingIdsUnique) : (step cfg decoder s b).1.PendingIdsUnique := by
  unfold step
  dsimp only
  split
  · exact h
  · exact (apply_freshIds cfg b.ap decoder s.state b.txs s.pending).unique

theorem Reachable.pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (genesis s : Snapshot)
    (hgenesis : genesis.PendingIdsUnique) (h : Reachable cfg decoder genesis s) : s.PendingIdsUnique := by
  induction h with
  | refl => exact hgenesis
  | step b _ _ ih => exact step_pendingIdsUnique cfg decoder _ b ih

theorem settle_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) (h : s.PendingIdsUnique) :
    (settle cfg decoder ap s fuel).snapshot.PendingIdsUnique := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
    unfold settle
    split
    · exact h
    · dsimp only
      have hs := step_pendingIdsUnique cfg decoder s { ap, txs := [] } h
      split
      · exact hs
      · exact ih _ hs

theorem runIsolated_pendingIdsUnique (cfg : RuntimeConfig) (decoder : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat) (h : s.PendingIdsUnique) :
    (runIsolated cfg decoder ap s txs fuel).snapshot.PendingIdsUnique := by
  unfold runIsolated
  dsimp only
  have hs := step_pendingIdsUnique cfg decoder s { ap, txs } h
  split
  · exact hs
  · exact settle_pendingIdsUnique cfg decoder ap _ fuel hs

end Near
