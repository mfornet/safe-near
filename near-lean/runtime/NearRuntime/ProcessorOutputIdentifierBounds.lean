import NearRuntime.FinalizedOutputIdentifierBounds

namespace Near
open Wasm.Near

/-- All ids carried by publicly emitted work are below the committed counter. -/
def Processed.OutputIdsBelowNext (processed : Processed) : Prop :=
  ∀ receipt ∈ processed.receipts, ∀ id ∈ receipt.liveIds, id < processed.state.nextId

theorem processDistribution_outputIds (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) : (processDistribution cfg ap st r g).OutputIdsBelowNext := by
  unfold processDistribution
  dsimp only
  repeat' (first
    | (intro candidate hm; exact absurd hm (List.not_mem_nil))
    | (intro candidate hm id hid
       simp only [List.mem_singleton] at hm
       subst candidate
       simp only [Receipt.liveIds, List.mem_singleton] at hid
       subst id
       exact Nat.lt_succ_self _)
    | split)

/-- Ready actions, waiting admission, data delivery and recursive resumption all
emit bounded receipt and dependency ids. Issues expose no speculative receipts.
Only input/state identifier bounds are required, not financial scope or success. -/
theorem processReceipt_outputIds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hstate : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).OutputIdsBelowNext := by
  cases hr : receipt.receipt with
  | action action =>
    cases hy : action.yieldDataId with
    | some dataId =>
      rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId hr hy]
      split <;> (intro candidate hm; contradiction)
    | none =>
      cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
      | false =>
        rw [processReceipt_waiting cfg ap decoder st receipt action hr hy he]
        intro candidate hm
        contradiction
      | true =>
        have hcallbacks : (readyActionContext cfg ap decoder st receipt action).CallbackIdsBelow
            (consumeReceiptDataState st action).nextId := by
          intro output hm
          apply hreceipt
          simp only [Receipt.liveIds, hr, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (List.mem_map.mpr ⟨output, hm, rfl⟩))
        rw [processReceipt_ready cfg ap decoder st receipt action hr hy he]
        unfold processedOfExec
        split
        · intro candidate hm; contradiction
        · exact applyActionReceipt_outputIds (readyActionContext cfg ap decoder st receipt action)
            (consumeReceiptDataState st action) hcallbacks
  | data data =>
    have hdata : data.dataId < st.nextId := hreceipt _ (by simp [Receipt.liveIds, hr])
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
      cases hroute : Assoc.lookup st.postponedByData data.dataId with
      | none => intro candidate hm; contradiction
      | some id =>
        simp only
        have hreceived := receivePostponedDataState_idsBelowNext st data hstate hdata
        cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
        | false => simp only [Bool.false_eq_true, ite_false]; intro candidate hm; contradiction
        | true =>
          simp only [ite_true]
          cases hwaiting : Assoc.lookup st.postponed id with
          | none => intro candidate hm; contradiction
          | some waiting =>
            have hw := ((ChainState.idsBelowNext_iff st).mp hstate).postponed (id, waiting)
              (Assoc.lookup_some_mem _ _ _ hwaiting)
            exact processReceipt_outputIds cfg ap decoder
              (releasePostponedState (receivePostponedDataState st data) id) waiting
              (releasePostponedState_idsBelowNext _ id hreceived) hw.2
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · intro candidate hm; contradiction
      · split
        · rename_i y hy
          split
          · rename_i a ha
            have hyl := ((ChainState.idsBelowNext_iff st).mp hstate).yields (receipt.receiverId, dataId, y)
              (Assoc.lookup_some_mem _ _ _ hy)
            have hbase := resumeYieldState_idsBelowNext st (receipt.receiverId, dataId) hstate
            rw [runActionReceipt_eq]
            unfold processedOfExec
            split
            · intro candidate hm; contradiction
            · refine applyActionReceipt_outputIds _ _ ?_
              intro output hm
              apply hyl
              simp only [Receipt.liveIds, ha, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inr (List.mem_map.mpr ⟨output, hm, rfl⟩))
          · intro candidate hm; contradiction
        · intro candidate hm; contradiction
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    exact processDistribution_outputIds cfg ap st receipt g
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

/-- One processor transition preserves the state bound and establishes the
bound on its complete public output list. This is not an ownership/uniqueness
invariant and places no liveness requirement on the emitted dependencies. -/
theorem processReceipt_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hstate : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).state.IdsBelowNext ∧
      (processReceipt cfg ap decoder st receipt).OutputIdsBelowNext :=
  ⟨processReceipt_idsBelowNext cfg ap decoder st receipt hstate hreceipt,
    processReceipt_outputIds cfg ap decoder st receipt hstate hreceipt⟩

/-- A receipt and the instant receipts it creates keep the state bound and bound every receipt sent out. -/
theorem processWithInstants_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (hstate : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processWithInstants cfg ap decoder st receipt).state.IdsBelowNext ∧
      (processWithInstants cfg ap decoder st receipt).OutputIdsBelowNext := by
  have key := processWithInstants_induction cfg ap decoder
    (fun acc pending => acc.state.IdsBelowNext ∧ acc.OutputIdsBelowNext ∧
      ∀ x ∈ pending, ∀ id ∈ x.liveIds, id < acc.state.nextId)
    (fun p => p.state.IdsBelowNext ∧ p.OutputIdsBelowNext)
    (fun st' r' => st' = st ∧ r' = receipt)
    (fun acc h => ⟨h.1, h.2.1⟩)
    (fun acc pending issue _ h => ⟨h.1, h.2.1⟩)
    (by
      intro acc r rest h hs hi
      obtain ⟨hst, hout, hpend⟩ := h
      have hb := processReceipt_identifier_bounds cfg { ap with storageAccounting := acc.storageAccounting } decoder
        acc.state r hst (hpend r (List.mem_cons_self))
      have hn := processReceipt_nextId_mono cfg { ap with storageAccounting := acc.storageAccounting } decoder
        acc.state r
      change (instantStep cfg ap decoder acc r).state.IdsBelowNext ∧
        (instantStep cfg ap decoder acc r).OutputIdsBelowNext at hb
      change acc.state.nextId ≤ (instantStep cfg ap decoder acc r).state.nextId at hn
      refine ⟨hb.1, ?_, ?_⟩
      · intro x hx id hid
        change x ∈ acc.receipts ++ (instantStep cfg ap decoder acc r).receipts.filter (fun x => !x.isInstant) at hx
        rcases List.mem_append.mp hx with hold | hnew
        · exact (hout x hold id hid).trans_le hn
        · exact hb.2 x (List.mem_filter.mp hnew).1 id hid
      · intro x hx id hid
        rcases List.mem_append.mp hx with hold | hnew
        · exact (hpend x (List.mem_cons_of_mem _ hold) id hid).trans_le hn
        · exact hb.2 x (List.mem_filter.mp hnew).1 id hid)
    (by
      rintro st' r' ⟨rfl, rfl⟩ hne
      exact processReceipt_identifier_bounds cfg ap decoder st r' hstate hreceipt)
    (by
      rintro st' r' ⟨rfl, rfl⟩ hi
      have hb := processReceipt_identifier_bounds cfg ap decoder st r' hstate hreceipt
      refine ⟨hb.1, ?_, ?_⟩
      · intro x hx id hid
        exact hb.2 x (List.mem_filter.mp hx).1 id hid
      · intro x hx id hid
        exact hb.2 x (List.mem_filter.mp hx).1 id hid)
  exact key st receipt ⟨rfl, rfl⟩

end Near
