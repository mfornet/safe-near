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

/-- An absent synthetic actor stays absent through the actual transaction,
receipt and gas-limit loops, including an early model-issue exit. -/
theorem applyAttempt_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : st.SystemAccountAbsent) :
    (applyAttempt cfg ap decoder st txs incoming).state.SystemAccountAbsent := by
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn txs _ _ : Id (ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat)) = txResult
  have htx : txResult.1.SystemAccountAbsent := by
    rw [← ht]
    refine forIn_id_preserves txs (st, [], [], 0, 0) _
      (fun s : ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat => s.1.SystemAccountAbsent) h ?_
    intro tx state hs
    cases hc : convertTransaction cfg ap state.1 tx with
    | error e => simpa only [hc] using hs
    | ok value =>
      obtain ⟨next, receipt, cost⟩ := value
      simpa only [hc] using convertTransaction_systemAbsent cfg ap state.1 next tx receipt cost hs hc
  generalize hq : (forIn (txResult.2.2.1 ++ txResult.1.delayed ++ incoming) _ _ : Id (Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool)) = result
  have hresult : result.2.1.SystemAccountAbsent ∧
      (∀ returned, result.1 = some returned → returned.state.SystemAccountAbsent) := by
    rw [← hq]
    apply forIn_id_preserves _ _ _
      (fun s : Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool =>
        s.2.1.SystemAccountAbsent ∧ ∀ returned, s.1 = some returned → returned.state.SystemAccountAbsent)
    · exact ⟨htx, by intro returned he; contradiction⟩
    · intro receipt state hs
      by_cases hover : state.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        exact ⟨hs.1, by intro returned he; contradiction⟩
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder state.2.1 receipt).issue with
        | some issue =>
          simp only
          exact ⟨hs.1, by intro returned he; cases he; exact h⟩
        | none =>
          simp only
          have hp := processReceipt_systemAbsent cfg ap decoder state.2.1 receipt hs.1
          cases hl : ap.gasLimit with
          | none => exact ⟨hp, by intro returned he; contradiction⟩
          | some limit =>
            simp only
            split_ifs <;> exact ⟨hp, by intro returned he; contradiction⟩
  split
  · rename_i returned he
    exact hresult.2 returned he
  · exact hresult.1

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
