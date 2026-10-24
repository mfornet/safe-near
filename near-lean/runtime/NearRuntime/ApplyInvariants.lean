import NearRuntime.ReservedActorInvariant

namespace Near
open Wasm.Near

/-- Induction over the executor's actual early-exit list loop. -/
theorem forIn_id_preserves {α β : Type} (xs : List α) (initial : β)
    (step : α → β → Id (ForInStep β)) (P : β → Prop) (hinitial : P initial)
    (hstep : ∀ x state, P state →
      match step x state with | .done next | .yield next => P next) :
    P (forIn xs initial step : Id β) := by
  induction xs generalizing initial with
  | nil => exact hinitial
  | cons x xs ih =>
    rw [List.forIn_cons]
    have h := hstep x initial hinitial
    cases he : step x initial with
    | done next => simpa only [he, bind, pure] using h
    | yield next => exact ih next (by simpa only [he, bind, pure] using h)

/-- Exact accumulator types of the two executable early-exit loops. -/
abbrev TransactionLoop := Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) ×
  List Receipt × List Receipt × Nat × Nat

abbrev ReceiptLoop := Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) ×
  List Receipt × List ReceiptIdentityBirth × Nat × Nat × List Receipt × List Receipt × Nat × Bool × Option TrieOverlay.State

/-- State predicates closed under the scheduler updates survive both real loops,
including atomic early exits and final assembly of retained/new delayed work. -/
theorem applyAttempt_state_predicate (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (P : ChainState → Prop)
    (htx : ∀ before after tx receipt cost, P before →
      convertTransaction cfg ap before tx = .ok (after, receipt, cost) → P after)
    (hreceipt : ∀ accounting before receipt, P before →
      P (processReceipt cfg { ap with storageAccounting := accounting } decoder before receipt).state)
    (hclear : ∀ before, P before → P { before with delayed := [] })
    (hdelay : ∀ before receipt, P before → P { before with delayed := before.delayed ++ [receipt] })
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (h : P st) :
    P (applyAttempt cfg ap decoder st txs incoming).state := by
  have happend (before : ChainState) (receipts : List Receipt) (hb : P before) :
      P { before with delayed := before.delayed ++ receipts } := by
    induction receipts generalizing before with
    | nil => simpa only [List.append_nil] using hb
    | cons receipt rest ih =>
      have hp := ih { before with delayed := before.delayed ++ [receipt] } (hdelay before receipt hb)
      simpa only [List.append_assoc, List.singleton_append] using hp
  have hdelays (before : ChainState) (receipts : List Receipt) (hb : P before) :
      P { before with delayed := receipts } := by
    simpa only [List.nil_append] using happend { before with delayed := [] } receipts (hclear before hb)
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn (chunkTransactions cfg txs) _ _ : Id TransactionLoop) = txResult
  have hconverted : P txResult.2.1 ∧ (∀ returned, txResult.1 = some returned → P returned.state) := by
    rw [← ht]
    apply forIn_id_preserves _ _ _
      (fun s : TransactionLoop => P s.2.1 ∧ ∀ returned, s.1 = some returned → P returned.state)
    · exact ⟨h, by intro returned he; contradiction⟩
    · intro tx state hs
      cases hc : convertTransaction cfg ap state.2.1 tx with
      | error error =>
        simp only
        cases hi : error.issue? with
        | some issue =>
          dsimp only
          exact ⟨hs.1, by intro returned he; cases he; exact h⟩
        | none =>
          dsimp only
          exact ⟨hs.1, by intro returned he; contradiction⟩
      | ok value =>
        obtain ⟨next, receipt, cost⟩ := value
        have hp := htx state.2.1 next tx receipt cost hs.1 hc
        simp only
        split_ifs <;> exact ⟨hp, by intro returned he; contradiction⟩
  split
  · rename_i returned he
    exact hconverted.2 returned he
  · generalize hq : (forIn ((txResult.2.2.2.2.1 ++ txResult.2.1.delayed ++ incoming).zipIdx) _ _ : Id ReceiptLoop) = result
    have hresult : P result.2.1 ∧ (∀ returned, result.1 = some returned → P returned.state) := by
      rw [← hq]
      apply forIn_id_preserves _ _ _
        (fun s : ReceiptLoop => P s.2.1 ∧ ∀ returned, s.1 = some returned → P returned.state)
      · exact ⟨hclear _ hconverted.1, by intro returned he; contradiction⟩
      · intro entry state hs
        by_cases hover : state.2.2.2.2.2.2.2.2.2.2.1 = true
        · simp only [hover, ite_true]
          split_ifs <;> exact ⟨hs.1, by intro returned he; contradiction⟩
        · simp only [hover, Bool.false_eq_true, ite_false]
          cases hi : (processReceipt cfg { ap with storageAccounting := state.2.2.2.2.2.2.2.2.2.2.2 } decoder state.2.1 entry.1).issue with
          | some issue =>
            simp only
            exact ⟨hs.1, by intro returned he; cases he; exact h⟩
          | none =>
            simp only
            have hp := hreceipt state.2.2.2.2.2.2.2.2.2.2.2 state.2.1 entry.1 hs.1
            cases hl : ap.gasLimit with
            | none =>
              simp only [hl] at hp
              exact ⟨hp, by intro returned he; contradiction⟩
            | some limit =>
              simp only [hl] at hp
              simp only
              split_ifs <;> exact ⟨hp, by intro returned he; contradiction⟩
    split
    · rename_i returned he
      exact hresult.2 returned he
    · exact hdelays _ _ hresult.1

/-- An absent synthetic actor stays absent through the actual transaction,
receipt and gas-limit loops, including an early model-issue exit. -/
theorem applyAttempt_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : st.SystemAccountAbsent) :
    (applyAttempt cfg ap decoder st txs incoming).state.SystemAccountAbsent := by
  apply applyAttempt_state_predicate cfg ap decoder ChainState.SystemAccountAbsent
  · exact convertTransaction_systemAbsent cfg ap
  · intro accounting; exact processReceipt_systemAbsent cfg { ap with storageAccounting := accounting } decoder
  · intro before hb; exact hb
  · intro before receipt hb; exact hb
  · exact h

theorem apply_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : st.SystemAccountAbsent) :
    (apply cfg ap decoder st txs incoming).state.SystemAccountAbsent := by
  unfold apply
  dsimp only
  split
  · exact h
  · exact applyAttempt_systemAbsent cfg ap decoder st txs incoming h

end Near
