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
    P (applyAttempt cfg ap decoder st txs incoming).state := by
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn txs _ _ : Id (ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat)) = txResult
  have htxResult : P txResult.1 := by
    rw [← ht]
    refine forIn_id_preserves txs (st, [], [], 0, 0) _
      (fun s : ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat => P s.1) h ?_
    intro tx state hs
    cases hc : convertTransaction cfg ap state.1 tx with
    | error error => simpa only [hc] using hs
    | ok value =>
      obtain ⟨next, receipt, cost⟩ := value
      simpa only [hc] using htx state.1 next tx receipt cost hs hc
  generalize hq : (forIn (txResult.2.2.1 ++ txResult.1.delayed ++ incoming) _ _ : Id (Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool)) = result
  have hresult : P result.2.1 ∧ (∀ returned, result.1 = some returned → P returned.state) := by
    rw [← hq]
    apply forIn_id_preserves _ _ _
      (fun s : Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool =>
        P s.2.1 ∧ ∀ returned, s.1 = some returned → P returned.state)
    · exact ⟨hclear _ htxResult, by intro returned he; contradiction⟩
    · intro receipt state hs
      by_cases hover : state.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        exact ⟨hdelay _ receipt hs.1, by intro returned he; contradiction⟩
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder state.2.1 receipt).issue with
        | some issue =>
          simp only
          exact ⟨hs.1, by intro returned he; cases he; exact h⟩
        | none =>
          simp only
          have hp := hreceipt state.2.1 receipt hs.1
          cases hl : ap.gasLimit with
          | none => exact ⟨hp, by intro returned he; contradiction⟩
          | some limit =>
            simp only
            split_ifs <;> exact ⟨hp, by intro returned he; contradiction⟩
  split
  · rename_i returned he
    exact hresult.2 returned he
  · exact hresult.1

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
