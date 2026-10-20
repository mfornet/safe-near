import NearRuntime.ActionIdentifierBounds

namespace Near
open Wasm.Near

theorem Assoc.lookup_some_mem {κ α : Type} [BEq κ] [LawfulBEq κ]
    (map : List (κ × α)) (key : κ) (value : α) (h : Assoc.lookup map key = some value) :
    (key, value) ∈ map := by
  unfold Assoc.lookup at h
  cases hf : map.find? (fun entry => entry.1 == key) with
  | none => simp [hf] at h
  | some entry =>
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have he : entry.1 = key := eq_of_beq hk
    cases entry with
    | mk found actual =>
      dsimp only at h he hm
      subst found
      subst actual
      exact hm

theorem consumeReceiptDataState_idsBelowNext (st : ChainState) (action : ActionReceipt) (h : st.IdsBelowNext) :
    (consumeReceiptDataState st action).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  constructor
  · exact h.postponed
  · exact h.pending
  · exact h.routes
  · intro entry hm
    exact h.received entry (List.mem_filter.mp hm).1
  · exact h.delayed

theorem receivedData_insert_idsBelowNext (st : ChainState) (data : DataReceipt)
    (h : st.IdsBelowNext) (hid : data.dataId < st.nextId) :
    ({ st with receivedData := Assoc.insert st.receivedData data.dataId data.data } : ChainState).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  exact ⟨h.postponed, h.pending, h.routes,
    Assoc.forall_insert _ _ _ _ h.received hid, h.delayed⟩

theorem pendingDataCount_insert_idsBelowNext (st : ChainState) (id : ReceiptId) (count : Nat)
    (h : st.IdsBelowNext) (hid : id < st.nextId) :
    ({ st with pendingDataCount := Assoc.insert st.pendingDataCount id count } : ChainState).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  exact ⟨h.postponed, Assoc.forall_insert _ _ _ _ h.pending hid, h.routes, h.received, h.delayed⟩

/-- All actual processor paths retain the state allocator bound. The incoming
receipt must use allocated ids; stored receipts inherit their bounds from the
initial state. No receipt-shape or successful-execution premise is needed. -/
theorem processReceipt_idsBelowNext (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (h : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).state.IdsBelowNext := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action hr he]
      exact postponeActionState_idsBelowNext st receipt action h hr hreceipt
    | true =>
      rw [processReceipt_ready cfg ap decoder st receipt action hr he]
      have hc := consumeReceiptDataState_idsBelowNext st action h
      unfold processedOfExec
      split
      · exact hc
      · exact applyActionReceipt_idsBelowNext _ _ hc
  | data data =>
    have hdata : data.dataId < st.nextId := hreceipt _ (by simp [Receipt.liveIds, hr])
    rw [processReceipt_data cfg ap decoder st receipt data hr]
    cases hroute : Assoc.lookup st.postponedByData data.dataId with
    | none => exact receivedData_insert_idsBelowNext st data h hdata
    | some id =>
      simp only
      have hreceived := receivePostponedDataState_idsBelowNext st data h hdata
      cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have hid := ((ChainState.idsBelowNext_iff st).mp h).routes (data.dataId, id)
          (Assoc.lookup_some_mem _ _ _ hroute)
        exact pendingDataCount_insert_idsBelowNext _ id _ hreceived hid.2
      | true =>
        simp only [ite_true]
        cases hwaiting : Assoc.lookup st.postponed id with
        | none => exact hreceived
        | some waiting =>
          have hw := ((ChainState.idsBelowNext_iff st).mp h).postponed (id, waiting)
            (Assoc.lookup_some_mem _ _ _ hwaiting)
          exact processReceipt_idsBelowNext cfg ap decoder
            (releasePostponedState (receivePostponedDataState st data) id) waiting
            (releasePostponedState_idsBelowNext _ id hreceived) hw.2
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

end Near
