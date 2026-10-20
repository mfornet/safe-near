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

/-- Selecting incoming receipts preserves structural financial premises. -/
theorem BlockFinancialPremises.filterIncoming (cfg : RuntimeConfig) (st : ChainState)
    (txs : List Transaction) (incoming : List Receipt) (select : Receipt → Bool)
    (h : BlockFinancialPremises cfg st txs incoming) :
    BlockFinancialPremises cfg st txs (incoming.filter select) := by
  have hs : List.Sublist (st.delayed ++ incoming.filter select) (st.delayed ++ incoming) :=
    List.Sublist.append_left List.filter_sublist _
  refine { h with incomingIds := ?_, queueUnique := ?_, queueDisjoint := ?_, queueShapes := ?_ }
  · intro receipt hm
    exact h.incomingIds receipt (List.mem_filter.mp hm).1
  · exact List.Nodup.sublist (hs.map _) h.queueUnique
  · intro receipt hm
    exact h.queueDisjoint receipt (hs.subset hm)
  · intro receipt hm
    exact h.queueShapes receipt (hs.subset hm)

/-- Retained and delivered receipts partition the same financial backing. -/
theorem receiptsFunds_filter_partition (cfg : RuntimeConfig) (receipts : List Receipt) (select : Receipt → Bool) :
    receiptsFunds cfg (receipts.filter select) + receiptsFunds cfg (receipts.filter (fun r => !select r)) =
      receiptsFunds cfg receipts := by
  induction receipts with
  | nil => rfl
  | cons receipt rest ih =>
    cases he : select receipt <;> simp [List.filter_cons, he, receiptsFunds] at * <;> omega

/-- One supported chain step conserves the account/in-flight ledger, including
receipts whose delivery is deferred, modulo net burn and explicit subsidy. -/
theorem step_conservation (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block)
    (h : BlockFinancialPremises cfg s.state b.txs s.pending)
    (hsupported : (step cfg decoder s b).2.issue = none) :
    (step cfg decoder s b).1.totalFunds cfg + (step cfg decoder s b).2.tokensBurnt =
      s.totalFunds cfg + (step cfg decoder s b).2.subsidizedAmount := by
  let select := fun receipt : Receipt => b.deliver receipt.receiptId
  let selected := s.pending.filter select
  let held := s.pending.filter (fun receipt => !select receipt)
  have ha : (apply cfg b.ap decoder s.state b.txs selected).issue = none := by
    simpa only [step_applyResult] using hsupported
  have hc := apply_conservation cfg b.ap decoder s.state b.txs selected
    (BlockFinancialPremises.filterIncoming cfg s.state b.txs s.pending select h) ha
  have hp := receiptsFunds_filter_partition cfg s.pending select
  have hs : (step cfg decoder s b).1.totalFunds cfg =
      (apply cfg b.ap decoder s.state b.txs selected).state.totalFunds cfg +
        receiptsFunds cfg held + receiptsFunds cfg (apply cfg b.ap decoder s.state b.txs selected).outgoing := by
    have ha' := ha
    dsimp only [selected, select] at ha'
    simp only [step, List.partition_eq_filter_filter, ha', Option.isSome_none, Bool.false_eq_true,
      ite_false, Snapshot.totalFunds_eq_runtime, receiptsFunds_append, selected, held, select, Function.comp_def]
    omega
  rw [hs, step_applyResult, Snapshot.totalFunds_eq_runtime]
  dsimp only [selected, held, select] at hc hp ⊢
  omega

end Near
