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
-- TODO(proof): adapt the cloned proof
theorem processReceipt_idsBelowNext (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (h : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).state.IdsBelowNext := by
  sorry

end Near
