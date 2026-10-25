import NearRuntime.DependencyIdentifierBounds

namespace Near
open Wasm.Near

/-- Component form of the live-id bound, useful for real routing map updates. -/
structure ChainState.RoutingIdsBelow (st : ChainState) (bound : Nat) : Prop where
  postponed : ∀ entry ∈ st.postponed, entry.1 < bound ∧ ∀ id ∈ entry.2.liveIds, id < bound
  pending : ∀ entry ∈ st.pendingDataCount, entry.1 < bound
  routes : ∀ entry ∈ st.postponedByData, entry.1 < bound ∧ entry.2 < bound
  received : ∀ entry ∈ st.receivedData, entry.1 < bound
  delayed : ∀ receipt ∈ st.delayed, ∀ id ∈ receipt.liveIds, id < bound
  yields : ∀ entry ∈ st.yieldReceipts, ∀ id ∈ entry.2.liveIds, id < bound

theorem ChainState.idsBelowNext_iff (st : ChainState) : st.IdsBelowNext ↔ st.RoutingIdsBelow st.nextId := by
  constructor
  · intro h
    constructor
    · intro entry hm
      constructor
      · apply h
        simp only [ChainState.liveIds, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨entry, hm, by simp⟩)))))
      · intro id hid
        apply h
        simp only [ChainState.liveIds, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨entry, hm, by simp [hid]⟩)))))
    · intro entry hm
      apply h
      simp only [ChainState.liveIds, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨entry, hm, rfl⟩)))))
    · intro entry hm
      constructor <;> apply h <;> simp only [ChainState.liveIds, List.mem_append]
      · exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨entry, hm, by simp⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨entry, hm, by simp⟩))))
    · intro entry hm
      apply h
      simp only [ChainState.liveIds, List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨entry, hm, rfl⟩)))
    · intro receipt hm id hid
      apply h
      simp only [ChainState.liveIds, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨receipt, hm, hid⟩))
    · intro entry hm id hid
      apply h
      simp only [ChainState.liveIds, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨entry, hm, hid⟩)
  · intro h id hm
    simp only [ChainState.liveIds, List.mem_append] at hm
    rcases hm with ((((hp | hn) | hr) | hd) | hdelayed) | hyield
    · obtain ⟨entry, he, hid⟩ := List.mem_flatMap.mp hp
      simp only [List.mem_cons] at hid
      rcases hid with rfl | hin
      · exact (h.postponed entry he).1
      · exact (h.postponed entry he).2 id hin
    · obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hn
      exact h.pending entry he
    · obtain ⟨entry, he, hid⟩ := List.mem_flatMap.mp hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hid
      rcases hid with rfl | rfl
      · exact (h.routes entry he).1
      · exact (h.routes entry he).2
    · obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hd
      exact h.received entry he
    · obtain ⟨receipt, he, hid⟩ := List.mem_flatMap.mp hdelayed
      exact h.delayed receipt he id hid
    · obtain ⟨entry, he, hid⟩ := List.mem_flatMap.mp hyield
      exact h.yields entry he id hid

theorem Assoc.forall_insert {κ α : Type} [BEq κ] (map : List (κ × α)) (key : κ) (value : α)
    (P : κ × α → Prop) (h : ∀ entry ∈ map, P entry) (hnew : P (key, value)) :
    ∀ entry ∈ Assoc.insert map key value, P entry := by
  intro entry hm
  simp only [Assoc.insert, List.mem_cons, List.mem_filter] at hm
  rcases hm with rfl | hm
  · exact hnew
  · exact h entry hm.1

theorem Assoc.forall_erase {κ α : Type} [BEq κ] (map : List (κ × α)) (key : κ)
    (P : κ × α → Prop) (h : ∀ entry ∈ map, P entry) :
    ∀ entry ∈ Assoc.erase map key, P entry := by
  intro entry hm
  exact h entry (List.mem_filter.mp hm).1

/-- Erasing a released receipt and its pending count cannot introduce any id. -/
theorem releasePostponedState_idsBelowNext (st : ChainState) (id : ReceiptId) (h : st.IdsBelowNext) :
    (releasePostponedState st id).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  constructor
  · exact Assoc.forall_erase st.postponed id _ h.postponed
  · exact Assoc.forall_erase st.pendingDataCount id _ h.pending
  · exact h.routes
  · exact h.received
  · exact h.delayed
  · exact h.yields

/-- Data delivery adds its already allocated dependency id and erases a route. -/
theorem receivePostponedDataState_idsBelowNext (st : ChainState) (data : DataReceipt)
    (h : st.IdsBelowNext) (hdata : data.dataId < st.nextId) :
    (receivePostponedDataState st data).IdsBelowNext := by
  rw [ChainState.idsBelowNext_iff] at h ⊢
  constructor
  · exact h.postponed
  · exact h.pending
  · exact Assoc.forall_erase st.postponedByData data.dataId _ h.routes
  · exact Assoc.forall_insert st.receivedData data.dataId data.data _ h.received hdata
  · exact h.delayed
  · exact h.yields

/-- List-loop preservation with the actual iteration-domain premise. -/
theorem foldl_preserves_mem (P : β → Prop) (step : β → α → β) (items : List α)
    (hstep : ∀ state item, item ∈ items → P state → P (step state item))
    (initial : β) (h : P initial) : P (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => exact h
  | cons item rest ih =>
    apply ih
    · intro state next hm hs
      exact hstep state next (by simp [hm]) hs
    · exact hstep initial item (by simp) h

/-- Waiting-action admission stores only the incoming receipt's allocated ids. -/
theorem postponeActionState_idsBelowNext (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (h : st.IdsBelowNext) (ha : receipt.receipt = .action action)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (postponeActionState st receipt action).IdsBelowNext := by
  have hrid : receipt.receiptId < st.nextId := hreceipt _ (by simp [Receipt.liveIds])
  have hinputs : ∀ id ∈ action.inputDataIds, id < st.nextId := by
    intro id hm
    apply hreceipt
    simp only [Receipt.liveIds, ha, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl hm)
  rw [ChainState.idsBelowNext_iff] at h ⊢
  constructor
  · exact Assoc.forall_insert st.postponed receipt.receiptId receipt _ h.postponed ⟨hrid, hreceipt⟩
  · exact Assoc.forall_insert st.pendingDataCount receipt.receiptId _ _ h.pending hrid
  · apply foldl_preserves_mem (fun map : List (DataId × ReceiptId) => ∀ entry ∈ map, entry.1 < st.nextId ∧ entry.2 < st.nextId)
    · intro map id hid hmap
      apply Assoc.forall_insert _ _ _ _ hmap
      exact ⟨hinputs id (List.mem_of_mem_filter hid), hrid⟩
    · exact h.routes
  · exact h.received
  · exact h.delayed
  · exact h.yields

end Near
