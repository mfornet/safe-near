import NearChain.PostponedOwnership

namespace Near
open Wasm.Near

/-- The chain's account/in-flight ledger is the runtime's queued ledger plus
inter-block pending receipts; this equality fixes the accounting boundary. -/
theorem Snapshot.totalFunds_eq_runtime (cfg : RuntimeConfig) (s : Snapshot) :
    s.totalFunds cfg = s.state.totalFunds cfg + receiptsFunds cfg s.pending := by
  simp only [Snapshot.totalFunds, Snapshot.inFlight, ChainState.totalFunds, ChainState.queuedFunds,
    ChainState.postponedFunds, Assoc.mass, receiptsFunds, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  omega

/-- One supported step conserves accounts and all in-flight work, including
receipts deferred by its delivery schedule. Structural scope is inherited from
the complete initial pending queue; no ledger equation is assumed. -/
theorem step_conservation (cfg : RuntimeConfig) (decoder : CodeTable) (s next : Snapshot) (b : Block)
    (result : ApplyResult) (hr : step cfg decoder s b = .ok (next, result))
    (h : BlockFinancialPremises cfg s.state b.txs s.pending) (hsupported : result.issue = none) :
    next.totalFunds cfg + result.tokensBurnt = s.totalFunds cfg + result.subsidizedAmount := by
  cases hs : b.receipts.resolve s.pending with
  | error error => simp [step, hs] at hr
  | ok pair =>
    obtain ⟨incoming, deferred⟩ := pair
    have hp := ReceiptSchedule.resolve_perm s.pending b.receipts incoming deferred hs
    have hmem : ∀ receipt ∈ s.state.delayed ++ incoming, receipt ∈ s.state.delayed ++ s.pending := by
      intro receipt hm
      rcases List.mem_append.mp hm with hd | hi
      · exact List.mem_append_left _ hd
      · exact List.mem_append_right _ (hp.mem_iff.mp (List.mem_append_left _ hi))
    have hselected : BlockFinancialPremises cfg s.state b.txs incoming := by
      refine ⟨h.accounts, h.postponed, h.identifiers, ?_, ?_, ?_, ?_, h.transactionActors,
        h.accountCostIncrease, h.rewardRatio⟩
      · intro receipt hm
        exact h.incomingIds receipt (hp.mem_iff.mp (List.mem_append_left _ hm))
      · have hn := ((List.Perm.append_left s.state.delayed hp).map (fun receipt : Receipt => receipt.receiptId)).nodup_iff.mpr h.queueUnique
        have hn' : (((s.state.delayed ++ incoming) ++ deferred).map (·.receiptId)).Nodup := by
          simpa only [List.append_assoc] using hn
        exact (List.nodup_append.mp (by simpa only [List.map_append] using hn')).1
      · intro receipt hm; exact h.queueDisjoint receipt (hmem receipt hm)
      · intro receipt hm; exact h.queueShapes receipt (hmem receipt hm)
    have hfunds : receiptsFunds cfg incoming + receiptsFunds cfg deferred = receiptsFunds cfg s.pending := by
      rw [← receiptsFunds_append]
      exact (hp.map (Fees.receiptFunds cfg)).sum_eq
    simp only [step, hs] at hr
    split at hr
    · cases hr
      simp_all
    · cases hr
      have hc := apply_conservation cfg b.ap decoder s.state b.txs incoming hselected hsupported
      rw [Snapshot.totalFunds_eq_runtime, Snapshot.totalFunds_eq_runtime]
      dsimp only
      rw [receiptsFunds_append]
      omega

end Near
