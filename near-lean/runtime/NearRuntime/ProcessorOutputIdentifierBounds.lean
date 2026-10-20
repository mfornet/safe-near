import NearRuntime.FinalizedOutputIdentifierBounds

namespace Near
open Wasm.Near

/-- All ids carried by publicly emitted work are below the committed counter. -/
def Processed.OutputIdsBelowNext (processed : Processed) : Prop :=
  ∀ receipt ∈ processed.receipts, ∀ id ∈ receipt.liveIds, id < processed.state.nextId

/-- Ready actions, waiting admission, data delivery and recursive resumption all
emit bounded receipt and dependency ids. Issues expose no speculative receipts.
Only input/state identifier bounds are required, not financial scope or success. -/
theorem processReceipt_outputIds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hstate : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).OutputIdsBelowNext := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action hr he]
      intro candidate hm
      contradiction
    | true =>
      have hcallbacks : (readyActionContext cfg ap decoder st receipt action).CallbackIdsBelow
          (consumeReceiptDataState st action).nextId := by
        intro output hm
        apply hreceipt
        simp only [Receipt.liveIds, hr, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨output, hm, rfl⟩))
      rw [processReceipt_ready cfg ap decoder st receipt action hr he]
      unfold processedOfExec
      split
      · intro candidate hm; contradiction
      · exact applyActionReceipt_outputIds (readyActionContext cfg ap decoder st receipt action)
          (consumeReceiptDataState st action) hcallbacks
  | data data =>
    have hdata : data.dataId < st.nextId := hreceipt _ (by simp [Receipt.liveIds, hr])
    rw [processReceipt_data cfg ap decoder st receipt data hr]
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

end Near
