import NearRuntime.AllocatorMonotonicity

namespace Near
open Wasm.Near

/-- Both actual block loops retain all ids allocated before the attempt. Early
model issues return the initial state; gas-limit deferral does not allocate. -/
theorem applyAttempt_nextId_mono (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    st.nextId ≤ (applyAttempt cfg ap decoder st txs incoming).state.nextId := by
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn txs _ _ : Id (ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat)) = txResult
  have htx : st.nextId ≤ txResult.1.nextId := by
    rw [← ht]
    refine forIn_id_preserves txs (st, [], [], 0, 0) _
      (fun s : ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat => st.nextId ≤ s.1.nextId)
      (Nat.le_refl _) ?_
    intro tx state hs
    cases hc : convertTransaction cfg ap state.1 tx with
    | error e => simpa only [hc] using hs
    | ok value =>
      obtain ⟨next, receipt, cost⟩ := value
      have hn := (convertTransaction_receipt_counter cfg ap state.1 next tx receipt cost hc).2
      have hp : state.1.nextId ≤ next.nextId := by omega
      simpa only [hc] using hs.trans hp
  generalize hq : (forIn (txResult.2.2.1 ++ txResult.1.delayed ++ incoming) _ _ : Id (Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool)) = result
  have hresult : st.nextId ≤ result.2.1.nextId ∧
      (∀ returned, result.1 = some returned → st.nextId ≤ returned.state.nextId) := by
    rw [← hq]
    apply forIn_id_preserves _ _ _
      (fun s : Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool =>
        st.nextId ≤ s.2.1.nextId ∧ ∀ returned, s.1 = some returned → st.nextId ≤ returned.state.nextId)
    · exact ⟨htx, by intro returned he; contradiction⟩
    · intro receipt state hs
      by_cases hover : state.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        exact ⟨hs.1, by intro returned he; contradiction⟩
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder state.2.1 receipt).issue with
        | some issue =>
          simp only
          exact ⟨hs.1, by intro returned he; cases he; exact Nat.le_refl _⟩
        | none =>
          simp only
          have hp := hs.1.trans (processReceipt_nextId_mono cfg ap decoder state.2.1 receipt)
          cases hl : ap.gasLimit with
          | none => exact ⟨hp, by intro returned he; contradiction⟩
          | some limit =>
            simp only
            split_ifs <;> exact ⟨hp, by intro returned he; contradiction⟩
  split
  · rename_i returned he
    exact hresult.2 returned he
  · exact hresult.1

/-- A public block application never rewinds the initial allocator, including
atomic unsupported/incomplete attempts. -/
theorem apply_nextId_mono (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    st.nextId ≤ (apply cfg ap decoder st txs incoming).state.nextId := by
  unfold apply
  dsimp only
  split
  · exact Nat.le_refl _
  · exact applyAttempt_nextId_mono cfg ap decoder st txs incoming

/-- Previously allocated external references remain bounded after processing a
receipt, even when that processing emits further work. -/
theorem processReceipt_retains_id_bound (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (id : Nat)
    (h : id < st.nextId) : id < (processReceipt cfg ap decoder st receipt).state.nextId :=
  h.trans_le (processReceipt_nextId_mono cfg ap decoder st receipt)

theorem apply_retains_id_bound (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (id : Nat)
    (h : id < st.nextId) : id < (apply cfg ap decoder st txs incoming).state.nextId :=
  h.trans_le (apply_nextId_mono cfg ap decoder st txs incoming)

end Near
