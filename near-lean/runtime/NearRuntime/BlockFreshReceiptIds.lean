import NearRuntime.ProcessedFreshReceiptIds

namespace Near
open Wasm.Near

def ApplyResult.FreshReceiptIds (lower : Nat) (result : ApplyResult) : Prop :=
  ReceiptList.FreshIds lower result.state.nextId result.outgoing

/-- The actual block accumulator appends disjoint allocation intervals for each
executed receipt. Early issues discard the accumulated output list atomically. -/
theorem applyAttempt_freshIds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    (applyAttempt cfg ap decoder st txs incoming).FreshReceiptIds st.nextId := by
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
    | error error => simpa only [hc] using hs
    | ok value =>
      obtain ⟨next, receipt, cost⟩ := value
      have hn := (convertTransaction_receipt_counter cfg ap state.1 next tx receipt cost hc).2
      have hmono : state.1.nextId ≤ next.nextId := by omega
      simpa only [hc] using hs.trans hmono
  generalize hq : (forIn (txResult.2.2.1 ++ txResult.1.delayed ++ incoming) _ _ : Id (Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool)) = result
  have hresult : st.nextId ≤ result.2.1.nextId ∧
      ReceiptList.FreshIds st.nextId result.2.1.nextId result.2.2.2.1 ∧
      (∀ returned, result.1 = some returned → returned.FreshReceiptIds st.nextId) := by
    rw [← hq]
    apply forIn_id_preserves _ _ _
      (fun s : Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool =>
        st.nextId ≤ s.2.1.nextId ∧ ReceiptList.FreshIds st.nextId s.2.1.nextId s.2.2.2.1 ∧
        ∀ returned, s.1 = some returned → returned.FreshReceiptIds st.nextId)
    · exact ⟨htx, ReceiptList.FreshIds.empty _ _, by intro returned he; contradiction⟩
    · intro receipt state hs
      by_cases hover : state.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        exact ⟨hs.1, hs.2.1, by intro returned he; contradiction⟩
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder state.2.1 receipt).issue with
        | some issue =>
          simp only
          refine ⟨hs.1, hs.2.1, ?_⟩
          intro returned he
          cases he
          exact ReceiptList.FreshIds.empty _ _
        | none =>
          simp only
          have hn := processReceipt_nextId_mono cfg ap decoder state.2.1 receipt
          have hout := ReceiptList.FreshIds.append hs.2.1
            (processReceipt_freshIds cfg ap decoder state.2.1 receipt) hs.1 hn
          have hmono := hs.1.trans hn
          cases hl : ap.gasLimit with
          | none => exact ⟨hmono, hout, by intro returned he; contradiction⟩
          | some limit =>
            simp only
            split_ifs <;> exact ⟨hmono, hout, by intro returned he; contradiction⟩
  split
  · rename_i returned he
    exact hresult.2.2 returned he
  · exact hresult.2.1

/-- A public block's outgoing envelope ids are distinct and allocated no earlier
than the initial counter, on supported and rejected attempts alike. -/
theorem apply_freshIds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    (apply cfg ap decoder st txs incoming).FreshReceiptIds st.nextId := by
  unfold apply
  dsimp only
  split
  · exact ReceiptList.FreshIds.empty _ _
  · exact applyAttempt_freshIds cfg ap decoder st txs incoming

/-- New outgoing envelopes cannot reuse any reference below the old counter. -/
theorem apply_outgoing_id_ne_old (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (receipt : Receipt) (hm : receipt ∈ (apply cfg ap decoder st txs incoming).outgoing)
    (id : Nat) (hid : id < st.nextId) : receipt.receiptId ≠ id := by
  have hl := ((apply_freshIds cfg ap decoder st txs incoming).bounds receipt hm).1
  intro he
  rw [he] at hl
  exact Nat.not_le_of_lt hid hl

end Near
