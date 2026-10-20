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

/-- One supported chain step conserves its full account/in-flight ledger,
modulo observed net burn and explicit subsidy, within the stated block scope. -/
theorem step_conservation (cfg : RuntimeConfig) (decoder : CodeTable) (s : Snapshot) (b : Block)
    (h : BlockFinancialPremises cfg s.state b.txs s.pending)
    (hsupported : (step cfg decoder s b).2.issue = none) :
    (step cfg decoder s b).1.totalFunds cfg + (step cfg decoder s b).2.tokensBurnt =
      s.totalFunds cfg + (step cfg decoder s b).2.subsidizedAmount := by
  have ha : (apply cfg b.ap decoder s.state b.txs s.pending).issue = none := by
    simpa only [step_applyResult] using hsupported
  have hc := apply_conservation cfg b.ap decoder s.state b.txs s.pending h ha
  simpa only [step, ha, Option.isSome_none, Bool.false_eq_true, ite_false, Snapshot.totalFunds_eq_runtime] using hc

end Near
