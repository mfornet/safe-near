import NearRuntime.BlockFreshReceiptIds

namespace Near
open Wasm.Near

/-- Every stored postponed payload agrees with its map key. This is independent
of financial scope, uniqueness, dependency-edge validity and scheduling fairness. -/
def ChainState.PostponedIdsMatch (st : ChainState) : Prop :=
  ∀ entry ∈ st.postponed, entry.2.receiptId = entry.1

theorem ChainState.PostponedIdsMatch.of_postponed_eq {before after : ChainState}
    (h : before.PostponedIdsMatch) (he : after.postponed = before.postponed) : after.PostponedIdsMatch := by
  intro entry hm
  exact h entry (he ▸ hm)

theorem postponeActionState_postponedIdsMatch (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (h : st.PostponedIdsMatch) : (postponeActionState st receipt action).PostponedIdsMatch :=
  Assoc.forall_insert st.postponed receipt.receiptId receipt _ h rfl

theorem releasePostponedState_postponedIdsMatch (st : ChainState) (id : ReceiptId)
    (h : st.PostponedIdsMatch) : (releasePostponedState st id).PostponedIdsMatch :=
  Assoc.forall_erase st.postponed id _ h

theorem releasePostponedState_keys_subset (st : ChainState) (id : ReceiptId) (key : ReceiptId)
    (hm : key ∈ (releasePostponedState st id).postponed.map Prod.fst) : key ∈ st.postponed.map Prod.fst := by
  obtain ⟨entry, he, hkey⟩ := List.mem_map.mp hm
  exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp he).1, hkey⟩

theorem postponeActionState_keys_subset (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (key : ReceiptId)
    (hm : key ∈ (postponeActionState st receipt action).postponed.map Prod.fst) :
    key ∈ st.postponed.map Prod.fst ∨ key = receipt.receiptId := by
  change key ∈ (Assoc.insert st.postponed receipt.receiptId receipt).map Prod.fst at hm
  simp only [Assoc.insert, List.map_cons, List.mem_cons] at hm
  rcases hm with he | hm
  · exact Or.inr he
  · obtain ⟨entry, he, hkey⟩ := List.mem_map.mp hm
    exact Or.inl (List.mem_map.mpr ⟨entry, (List.mem_filter.mp he).1, hkey⟩)

/-- The real processor preserves stored identity agreement and creates no
postponed key other than the incoming receipt's own identity. Recursive data
resumption may reinsert only a previously owned postponed identity. -/
theorem processReceipt_postponed_ownership (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (h : st.PostponedIdsMatch) :
    (processReceipt cfg ap decoder st receipt).state.PostponedIdsMatch ∧
      ∀ key ∈ (processReceipt cfg ap decoder st receipt).state.postponed.map Prod.fst,
        key ∈ st.postponed.map Prod.fst ∨ key = receipt.receiptId := by
  cases hr : receipt.receipt with
  | action action =>
    cases hy : action.yieldDataId with
    | some dataId =>
      rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId hr hy]
      split
      · exact ⟨h, fun key hm => Or.inl hm⟩
      · exact ⟨h, fun key hm => Or.inl hm⟩
    | none =>
      cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
      | false =>
        rw [processReceipt_waiting cfg ap decoder st receipt action hr hy he]
        exact ⟨postponeActionState_postponedIdsMatch st receipt action h,
          postponeActionState_keys_subset st receipt action⟩
      | true =>
        have hf := congrArg Prod.fst (processReceipt_ready_receiptQueues cfg ap decoder st receipt action hr hy he)
        change (processReceipt cfg ap decoder st receipt).state.postponed = st.postponed at hf
        exact ⟨h.of_postponed_eq hf, fun key hm => Or.inl (by simpa only [hf] using hm)⟩
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
      cases hroute : Assoc.lookup st.postponedByData data.dataId with
      | none => exact ⟨h, fun key hm => Or.inl hm⟩
      | some id =>
        simp only
        cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
        | false => simp only [Bool.false_eq_true, ite_false]; exact ⟨h, fun key hm => Or.inl hm⟩
        | true =>
          simp only [ite_true]
          cases hwaiting : Assoc.lookup st.postponed id with
          | none => exact ⟨h, fun key hm => Or.inl hm⟩
          | some waiting =>
            have hm := Assoc.lookup_some_mem _ _ _ hwaiting
            have hid := h (id, waiting) hm
            change waiting.receiptId = id at hid
            have hi := processReceipt_postponed_ownership cfg ap decoder
              (releasePostponedState (receivePostponedDataState st data) id) waiting
              (releasePostponedState_postponedIdsMatch _ id h)
            refine ⟨hi.1, ?_⟩
            intro key hkey
            rcases hi.2 key hkey with hold | hnew
            · exact Or.inl (releasePostponedState_keys_subset _ id key hold)
            · exact Or.inl (List.mem_map.mpr ⟨(id, waiting), hm, by simpa only [hid] using hnew.symm⟩)
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · exact ⟨h, fun key hm => Or.inl hm⟩
      · split
        · rename_i y _
          split
          · rename_i a _
            have hq := runActionReceipt_receiptQueues cfg ap decoder
              (resumeYieldState st (receipt.receiverId, dataId)) y a [data.promiseResult]
            have hf := congrArg Prod.fst hq
            change (runActionReceipt cfg ap decoder (resumeYieldState st (receipt.receiverId, dataId)) y a
              [data.promiseResult]).state.postponed = st.postponed at hf
            exact ⟨h.of_postponed_eq hf, fun key hm => Or.inl (by simpa only [hf] using hm)⟩
          · exact ⟨h, fun key hm => Or.inl hm⟩
        · exact ⟨h, fun key hm => Or.inl hm⟩
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    have hadv := processDistribution_advance cfg ap st receipt g
    exact ⟨h.of_postponed_eq hadv.1, fun key hm => Or.inl (by simpa only [hadv.1] using hm)⟩
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

/-- An instant receipt never waits for data, so it leaves the postponed map alone. -/
theorem processReceipt_instant_postponed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hinst : receipt.isInstant = true) :
    (processReceipt cfg ap decoder st receipt).state.postponed = st.postponed := by
  obtain ⟨a, hr, hcase⟩ := Receipt.isInstant_action hinst
  cases hy : a.yieldDataId with
  | some dataId =>
    rw [processReceipt_yield_unfold cfg ap decoder st receipt a dataId hr hy]
    split <;> rfl
  | none =>
    have hempty : a.inputDataIds = [] := by
      rcases hcase with h | h
      · simp [hy] at h
      · exact h
    have hready : (a.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true := by
      simp [hempty]
    exact congrArg Prod.fst (processReceipt_ready_receiptQueues cfg ap decoder st receipt a hr hy hready)

/-- The receipt and the instant receipts it creates preserve stored identity agreement and create
no postponed key other than the incoming receipt's own identity. -/
theorem processWithInstants_postponed_ownership (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (h : st.PostponedIdsMatch) :
    (processWithInstants cfg ap decoder st receipt).state.PostponedIdsMatch ∧
      ∀ key ∈ (processWithInstants cfg ap decoder st receipt).state.postponed.map Prod.fst,
        key ∈ st.postponed.map Prod.fst ∨ key = receipt.receiptId := by
  have key := processWithInstants_induction cfg ap decoder
    (fun acc pending => acc.state.PostponedIdsMatch ∧
      (∀ key ∈ acc.state.postponed.map Prod.fst, key ∈ st.postponed.map Prod.fst ∨ key = receipt.receiptId) ∧
      ∀ x ∈ pending, x.isInstant = true)
    (fun p => p.state.PostponedIdsMatch ∧
      ∀ key ∈ p.state.postponed.map Prod.fst, key ∈ st.postponed.map Prod.fst ∨ key = receipt.receiptId)
    (fun st' r' => st' = st ∧ r' = receipt)
    (fun acc h => ⟨h.1, h.2.1⟩)
    (fun acc pending issue _ h => ⟨h.1, h.2.1⟩)
    (by
      intro acc r rest h hs hi
      obtain ⟨hm, hk, hpend⟩ := h
      have hinst := hpend r (List.mem_cons_self)
      have hp := processReceipt_postponed_ownership cfg { ap with storageAccounting := acc.storageAccounting }
        decoder acc.state r hm
      have heq := processReceipt_instant_postponed cfg { ap with storageAccounting := acc.storageAccounting }
        decoder acc.state r hinst
      change (instantStep cfg ap decoder acc r).state.postponed = acc.state.postponed at heq
      change (instantStep cfg ap decoder acc r).state.PostponedIdsMatch ∧ _ at hp
      refine ⟨hp.1, ?_, ?_⟩
      · intro key hkm
        change key ∈ (instantStep cfg ap decoder acc r).state.postponed.map Prod.fst at hkm
        rw [heq] at hkm
        exact hk key hkm
      · intro x hx
        rcases List.mem_append.mp hx with hold | hnew
        · exact hpend x (List.mem_cons_of_mem _ hold)
        · exact (List.mem_filter.mp hnew).2)
    (by
      rintro st' r' ⟨rfl, rfl⟩ hne
      exact processReceipt_postponed_ownership cfg ap decoder st' r' h)
    (by
      rintro st' r' ⟨rfl, rfl⟩ hi
      have hp := processReceipt_postponed_ownership cfg ap decoder st' r' h
      exact ⟨hp.1, hp.2, fun x hx => (List.mem_filter.mp hx).2⟩)
  exact key st receipt ⟨rfl, rfl⟩

theorem Assoc.key_not_mem_of_lookup_none {κ α : Type} [BEq κ] [LawfulBEq κ]
    (map : List (κ × α)) (key : κ) (h : Assoc.lookup map key = none) : key ∉ map.map Prod.fst := by
  induction map with
  | nil => simp
  | cons entry rest ih =>
    by_cases he : entry.1 = key
    · simp [Assoc.lookup, he] at h
    · have ht : Assoc.lookup rest key = none := by simpa [Assoc.lookup, he] using h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm he, ih ht⟩

theorem Assoc.lookup_of_mem_unique {κ α : Type} [BEq κ] [LawfulBEq κ]
    (map : List (κ × α)) (key : κ) (value : α) (hunique : Assoc.KeysUnique map)
    (hmem : (key, value) ∈ map) : Assoc.lookup map key = some value := by
  induction map with
  | nil => contradiction
  | cons entry rest ih =>
    have hn : entry.1 ∉ rest.map Prod.fst ∧ Assoc.KeysUnique rest := by
      simpa [Assoc.KeysUnique] using hunique
    rcases List.mem_cons.mp hmem with he | hrest
    · subst entry
      simp [Assoc.lookup]
    · have hne : entry.1 ≠ key := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨(key, value), hrest, he.symm⟩)
      simpa [Assoc.lookup, hne] using ih hn.2 hrest

/-- The existing financial map invariant supplies identity agreement; callers
need not assume a second independent property when applying these lemmas. -/
theorem ChainState.PostponedFinancialWellFormed.idsMatch {st : ChainState}
    (h : st.PostponedFinancialWellFormed) : st.PostponedIdsMatch := by
  intro entry hm
  exact (h.entries entry.1 entry.2 (Assoc.lookup_of_mem_unique _ _ _ h.unique hm)).1

/-- Processing cannot occupy a different previously empty postponed slot. -/
theorem processReceipt_postponed_lookup_none (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (key : ReceiptId) (h : st.PostponedIdsMatch)
    (hempty : Assoc.lookup st.postponed key = none) (hne : receipt.receiptId ≠ key) :
    Assoc.lookup (processReceipt cfg ap decoder st receipt).state.postponed key = none := by
  apply Assoc.lookup_none_of_key_not_mem
  intro hm
  rcases (processReceipt_postponed_ownership cfg ap decoder st receipt h).2 key hm with hold | he
  · exact Assoc.key_not_mem_of_lookup_none _ _ hempty hold
  · exact hne he.symm

/-- Minimal admission invariant for a fixed queue: identities are distinct,
postponed payloads agree with their keys, and no queued receipt is already owned
by a postponed slot. Delayed ownership and complete graph validity are separate. -/
structure ReceiptQueue.PostponedAdmission (st : ChainState) (receipts : List Receipt) : Prop where
  storedIdsMatch : st.PostponedIdsMatch
  unique : (receipts.map (·.receiptId)).Nodup
  disjoint : ∀ receipt ∈ receipts, Assoc.lookup st.postponed receipt.receiptId = none

/-- After the actual processor consumes the head, every remaining receipt keeps
its empty postponed slot. This supplies the non-overwrite premise needed to
compose local receipt conservation; it is not an assumed financial equation. -/
theorem ReceiptQueue.PostponedAdmission.after_process (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (rest : List Receipt)
    (h : ReceiptQueue.PostponedAdmission st (receipt :: rest)) :
    ReceiptQueue.PostponedAdmission (processReceipt cfg ap decoder st receipt).state rest := by
  have hn : receipt.receiptId ∉ rest.map (·.receiptId) ∧ (rest.map (·.receiptId)).Nodup := by
    simpa only [List.map_cons, List.nodup_cons] using h.unique
  refine ⟨(processReceipt_postponed_ownership cfg ap decoder st receipt h.storedIdsMatch).1, hn.2, ?_⟩
  intro next hm
  apply processReceipt_postponed_lookup_none cfg ap decoder st receipt next.receiptId h.storedIdsMatch
  · exact h.disjoint next (by simp [hm])
  · intro he
    exact hn.1 (List.mem_map.mpr ⟨next, hm, he.symm⟩)

/-- The lifted form for a receipt together with the instant receipts it creates. -/
theorem processWithInstants_postponed_lookup_none (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (key : ReceiptId)
    (h : st.PostponedIdsMatch) (hempty : Assoc.lookup st.postponed key = none) (hne : receipt.receiptId ≠ key) :
    Assoc.lookup (processWithInstants cfg ap decoder st receipt).state.postponed key = none := by
  apply Assoc.lookup_none_of_key_not_mem
  intro hm
  rcases (processWithInstants_postponed_ownership cfg ap decoder st receipt h).2 key hm with hold | he
  · exact Assoc.key_not_mem_of_lookup_none _ _ hempty hold
  · exact hne he.symm

theorem ReceiptQueue.PostponedAdmission.after_processWithInstants (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (rest : List Receipt)
    (h : ReceiptQueue.PostponedAdmission st (receipt :: rest)) :
    ReceiptQueue.PostponedAdmission (processWithInstants cfg ap decoder st receipt).state rest := by
  have hn : receipt.receiptId ∉ rest.map (·.receiptId) ∧ (rest.map (·.receiptId)).Nodup := by
    simpa only [List.map_cons, List.nodup_cons] using h.unique
  refine ⟨(processWithInstants_postponed_ownership cfg ap decoder st receipt h.storedIdsMatch).1, hn.2, ?_⟩
  intro next hm
  apply processWithInstants_postponed_lookup_none cfg ap decoder st receipt next.receiptId h.storedIdsMatch
  · exact h.disjoint next (by simp [hm])
  · intro he
    exact hn.1 (List.mem_map.mpr ⟨next, hm, he.symm⟩)

end Near
