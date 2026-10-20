import NearRuntime.PostponedOwnership

namespace Near
open Wasm.Near

/-- A reusable induction rule for the actual block executor. The premises are
local preservation rules for transactions, receipt processing and the two
scheduler updates; early issue rollback is handled by the theorem itself. -/
theorem applyAttempt_preserves_state (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (P : ChainState → Prop)
    (htx : ∀ before after tx receipt cost, P before →
      convertTransaction cfg ap before tx = .ok (after, receipt, cost) → P after)
    (hreceipt : ∀ before receipt, P before → P (processReceipt cfg ap decoder before receipt).state)
    (hclear : ∀ before, P before → P { before with delayed := [] })
    (hdelay : ∀ before receipt, P before → P { before with delayed := before.delayed ++ [receipt] })
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (h : P st) :
    P (applyAttempt cfg ap decoder st txs incoming).state :=
  applyAttempt_state_predicate cfg ap decoder P htx hreceipt hclear hdelay st txs incoming h

theorem apply_preserves_state (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (P : ChainState → Prop)
    (htx : ∀ before after tx receipt cost, P before →
      convertTransaction cfg ap before tx = .ok (after, receipt, cost) → P after)
    (hreceipt : ∀ before receipt, P before → P (processReceipt cfg ap decoder before receipt).state)
    (hclear : ∀ before, P before → P { before with delayed := [] })
    (hdelay : ∀ before receipt, P before → P { before with delayed := before.delayed ++ [receipt] })
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (h : P st) :
    P (apply cfg ap decoder st txs incoming).state := by
  unfold apply
  dsimp only
  split
  · exact h
  · exact applyAttempt_preserves_state cfg ap decoder P htx hreceipt hclear hdelay st txs incoming h

theorem convertTransaction_postponedIdsMatch (cfg : RuntimeConfig) (ap : ApplyState)
    (before after : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : before.PostponedIdsMatch) (hc : convertTransaction cfg ap before tx = .ok (after, receipt, cost)) :
    after.PostponedIdsMatch := by
  obtain ⟨signer, key, _, _, hcommit, _⟩ := convertTransaction_success_commit cfg ap before after tx receipt cost hc
  have hf := congrArg (fun result => result.1.postponed) hcommit
  exact h.of_postponed_eq hf.symm

/-- Stored receipt/key agreement survives a complete block without financial-
shape, uniqueness or success premises. -/
theorem apply_postponedIdsMatch (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (h : st.PostponedIdsMatch) : (apply cfg ap decoder st txs incoming).state.PostponedIdsMatch := by
  apply apply_preserves_state cfg ap decoder ChainState.PostponedIdsMatch
  · exact convertTransaction_postponedIdsMatch cfg ap
  · intro before receipt hb
    exact (processReceipt_postponed_ownership cfg ap decoder before receipt hb).1
  · intro before hb; exact hb
  · intro before receipt hb; exact hb
  · exact h

end Near
