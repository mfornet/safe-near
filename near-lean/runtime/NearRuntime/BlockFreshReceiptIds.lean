import NearRuntime.ProcessedFreshReceiptIds

namespace Near
open Wasm.Near

def ApplyResult.FreshReceiptIds (lower : Nat) (result : ApplyResult) : Prop :=
  ReceiptList.FreshIds lower result.state.nextId result.outgoing

structure TransactionLoop.FreshInvariant (lower : Nat) (pass : TransactionLoop) : Prop where
  counter : lower ≤ pass.2.1.nextId
  outgoing : ReceiptList.FreshIds lower pass.2.1.nextId pass.2.2.2.1
  returned : ∀ result, pass.1 = some result → result.FreshReceiptIds lower

structure ReceiptLoop.FreshInvariant (lower : Nat) (pass : ReceiptLoop) : Prop where
  counter : lower ≤ pass.2.1.nextId
  outgoing : ReceiptList.FreshIds lower pass.2.1.nextId pass.2.2.2.1
  returned : ∀ result, pass.1 = some result → result.FreshReceiptIds lower

theorem resolveYieldTimeouts_freshIds (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) (lower : Nat)
    (outgoing : List Receipt) :
    ∀ (acc : ChainState × List Receipt × List ReceiptIdentityBirth), lower ≤ acc.1.nextId →
      ReceiptList.FreshIds lower acc.1.nextId (outgoing ++ acc.2.1) →
      ReceiptList.FreshIds lower (resolveYieldTimeouts ap limit used fuel acc).1.nextId
        (outgoing ++ (resolveYieldTimeouts ap limit used fuel acc).2.1) := by
  induction fuel with
  | zero => intro acc _ h; exact h
  | succ fuel ih =>
    rintro ⟨st, receipts, births⟩ hl h
    unfold resolveYieldTimeouts
    dsimp only at hl h ⊢
    split
    · exact h
    · split
      · split
        · exact h
        · split
          · exact h
          · split
            · apply ih
              · exact hl.trans (Nat.le_succ _)
              · rw [← List.append_assoc]
                apply ReceiptList.FreshIds.append h _ hl (Nat.le_succ _)
                constructor
                · simp
                · intro receipt hm
                  have he := List.mem_singleton.mp hm
                  subst receipt
                  exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
            · exact ih _ hl h
      · exact h

theorem timeouts_freshIds (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) (lower : Nat)
    (st : ChainState) (outgoing : List Receipt) (hl : lower ≤ st.nextId)
    (hout : ReceiptList.FreshIds lower st.nextId outgoing) :
    ReceiptList.FreshIds lower (resolveYieldTimeouts ap limit used fuel (st, [], [])).1.nextId
      (outgoing ++ (resolveYieldTimeouts ap limit used fuel (st, [], [])).2.1) :=
  resolveYieldTimeouts_freshIds ap limit used fuel lower outgoing (st, [], []) hl (by simpa using hout)

/-- The actual block accumulator appends disjoint allocation intervals for
nonlocal transactions and executed receipts. Early issues discard output atomically. -/
theorem applyAttempt_freshIds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    (applyAttempt cfg ap decoder st txs incoming).FreshReceiptIds st.nextId := by
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn txs _ _ : Id TransactionLoop) = txResult
  have htx : TransactionLoop.FreshInvariant st.nextId txResult := by
    rw [← ht]
    apply forIn_id_preserves _ _ _ (TransactionLoop.FreshInvariant st.nextId)
    · exact ⟨Nat.le_refl _, ReceiptList.FreshIds.empty _ _, by intro result he; contradiction⟩
    · intro tx pass h
      cases hc : convertTransaction cfg ap pass.2.1 tx with
      | error error =>
        dsimp only
        cases hi : error.issue? with
        | some issue =>
          dsimp only
          exact ⟨h.counter, h.outgoing, by intro result he; cases he; exact ReceiptList.FreshIds.empty _ _⟩
        | none =>
          dsimp only
          exact ⟨h.counter, h.outgoing, by intro result he; contradiction⟩
      | ok value =>
        obtain ⟨next, receipt, cost⟩ := value
        have hn := convertTransaction_receipt_counter cfg ap pass.2.1 next tx receipt cost hc
        have hmono : pass.2.1.nextId ≤ next.nextId := by omega
        have hsingle : ReceiptList.FreshIds pass.2.1.nextId next.nextId [receipt] := by
          constructor
          · simp
          · intro candidate hm
            have he := List.mem_singleton.mp hm
            subst candidate
            rw [hn.1, hn.2]
            exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
        dsimp only
        split_ifs
        · exact ⟨h.counter.trans hmono, h.outgoing.mono_upper hmono, by intro result he; contradiction⟩
        · exact ⟨h.counter.trans hmono, h.outgoing.append hsingle h.counter hmono,
            by intro result he; contradiction⟩
  split
  · rename_i returned he
    exact htx.returned returned he
  · generalize hq : (forIn (txResult.2.2.2.2.1 ++ txResult.2.1.delayed ++ incoming).zipIdx _ _ : Id ReceiptLoop) = result
    have hresult : ReceiptLoop.FreshInvariant st.nextId result := by
      rw [← hq]
      apply forIn_id_preserves _ _ _ (ReceiptLoop.FreshInvariant st.nextId)
      · exact ⟨htx.counter, htx.outgoing, by intro returned he; contradiction⟩
      · intro entry pass h
        by_cases hover : pass.2.2.2.2.2.2.2.2.2.2.1 = true
        · simp only [hover, ite_true]
          split_ifs <;> exact ⟨h.counter, h.outgoing, by intro returned he; contradiction⟩
        · simp only [hover, Bool.false_eq_true, ite_false]
          cases hi : (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1).issue with
          | some issue =>
            dsimp only
            exact ⟨h.counter, h.outgoing,
              by intro returned he; cases he; exact ReceiptList.FreshIds.empty _ _⟩
          | none =>
            dsimp only
            have hn := processWithInstants_nextId_mono cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1
            have hout := h.outgoing.append
              (processWithInstants_freshIds cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 entry.1) h.counter hn
            cases hl : ap.gasLimit with
            | none =>
              simp only [hl] at hn hout
              exact ⟨h.counter.trans hn, hout, by intro returned he; contradiction⟩
            | some limit =>
              simp only [hl] at hn hout
              dsimp only
              split_ifs <;> exact ⟨h.counter.trans hn, hout, by intro returned he; contradiction⟩
    split
    · rename_i returned he
      exact hresult.returned returned he
    · exact timeouts_freshIds ap ap.gasLimit _ _ st.nextId _ _ hresult.counter hresult.outgoing

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
