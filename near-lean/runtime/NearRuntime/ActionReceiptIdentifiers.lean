import NearRuntime.DataReceiptIdentifiers

namespace Near
open Wasm.Near

theorem foldl_append_map (view : β → List γ) (step : β → α → β) (value : α → γ)
    (hstep : ∀ state item, view (step state item) = view state ++ [value item])
    (items : List α) (initial : β) :
    view (items.foldl step initial) = view initial ++ items.map value := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    rw [List.foldl_cons, ih, hstep]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- Action emission uses the preallocated envelope ids, in promise order. -/
theorem emitFunctionCallActions_receiptIds (c : ReceiptCtx) (specs : List ReceiptSpec)
    (ids : Array ReceiptId) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (receipts : List Receipt) :
    (emitFunctionCallActions c specs ids outputs inputs receipts).map (·.receiptId) =
      receipts.map (·.receiptId) ++ (List.range' 0 specs.length).map (fun i => ids[i]?.getD 0) := by
  simp only [emitFunctionCallActions, Std.Legacy.Range.forIn'_eq_forIn'_range',
    List.forIn'_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  trans receipts.map (·.receiptId) ++
    ((List.range' 0 specs.length).attach.map fun i => ids[i.val]?.getD 0)
  · apply foldl_append_map
    intro state item
    simp only [List.map_append, List.map_cons, List.map_nil]
  · rw [List.attach_map_val (f := fun i => ids[i]?.getD 0)]

/-- A correctly sized preallocation has no default-id fallback during emission. -/
theorem receiptIdArray_range (ids : Array ReceiptId) :
    (List.range' 0 ids.size).map (fun i => ids[i]?.getD 0) = ids.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    simp at hi
    simp [hi]

/-- Allocating and emitting promises retains exactly the allocated fresh range. -/
theorem emitFunctionCallActions_allocated_receiptIds (c : ReceiptCtx) (specs : List ReceiptSpec)
    (initial : ChainState) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (receipts : List Receipt) :
    (emitFunctionCallActions c specs (allocateFunctionCallIds specs initial).2 outputs inputs receipts).map (·.receiptId) =
      receipts.map (·.receiptId) ++ List.range' initial.nextId specs.length := by
  rw [emitFunctionCallActions_receiptIds]
  have hsize : (allocateFunctionCallIds specs initial).2.size = specs.length := by
    have hl := congrArg List.length (allocateFunctionCallIds_ids specs initial #[])
    simpa using hl
  rw [← hsize, receiptIdArray_range, allocateFunctionCallIds_ids]
  simp only [List.nil_append, hsize]

/-- Newly emitted action envelopes have unique receipt identities. -/
theorem emitFunctionCallActions_allocated_nodup (c : ReceiptCtx) (specs : List ReceiptSpec)
    (initial : ChainState) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId)) :
    ((emitFunctionCallActions c specs (allocateFunctionCallIds specs initial).2 outputs inputs).map (·.receiptId)).Nodup := by
  rw [emitFunctionCallActions_allocated_receiptIds]
  simpa using List.nodup_range' (s := initial.nextId) (n := specs.length)

/-- The count of immediate return-data envelopes. A returned promise forwards
its output receivers instead of emitting those data receipts immediately. -/
def immediateDataCount (outcome : VMOutcome) (c : ReceiptCtx) (isLast : Bool) : Nat :=
  match outcome.returnData with
  | .receiptIndex _ => 0
  | _ => if isLast then c.action.outputDataReceivers.length else 0

/-- Exact envelope ids of the complete executable materializer: immediate data
first, then promise actions. Dependency allocation separates the two ranges. -/
theorem materializeFunctionCall_receiptIds (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    ((materializeFunctionCall c isLast outcome initial).receipts.map (·.receiptId)) =
      List.range' (initial.nextId + outcome.receipts.length +
        (outcome.receipts.map fun spec => spec.dependencies.length).sum) (immediateDataCount outcome c isLast) ++
      List.range' initial.nextId outcome.receipts.length := by
  rw [materializeFunctionCall_eq_stages]
  cases hr : outcome.returnData <;> cases isLast <;>
    simp [hr, emitFunctionCallActions_allocated_receiptIds, emitFunctionCallData_receiptIds,
      linkFunctionCallDependencies_nextId, allocateFunctionCallIds_nextId, immediateDataCount]

/-- Every emitted envelope has a unique identity, including simultaneous data
and action emission. No VM-provided id freshness premise is needed. -/
theorem materializeFunctionCall_receiptIds_nodup (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    ((materializeFunctionCall c isLast outcome initial).receipts.map (·.receiptId)).Nodup := by
  rw [materializeFunctionCall_receiptIds, List.nodup_append]
  refine ⟨List.nodup_range', List.nodup_range', ?_⟩
  intro dataId hdata actionId haction he
  subst actionId
  have hd := List.mem_range'_1.mp hdata
  have ha := List.mem_range'_1.mp haction
  omega

/-- The complete materializer allocates every emitted receipt identity within
its own counter interval, despite emitting data before actions. -/
theorem materializeFunctionCall_receiptId_bounds (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (receipt : Receipt)
    (hmem : receipt ∈ (materializeFunctionCall c isLast outcome initial).receipts) :
    initial.nextId ≤ receipt.receiptId ∧
      receipt.receiptId < (materializeFunctionCall c isLast outcome initial).state.nextId := by
  have hm : receipt.receiptId ∈ ((materializeFunctionCall c isLast outcome initial).receipts.map (·.receiptId)) :=
    List.mem_map.mpr ⟨receipt, hmem, rfl⟩
  rw [materializeFunctionCall_receiptIds, List.mem_append] at hm
  have hn : (materializeFunctionCall c isLast outcome initial).state.nextId =
      initial.nextId + outcome.receipts.length +
        (outcome.receipts.map fun spec => spec.dependencies.length).sum + immediateDataCount outcome c isLast := by
    have he := materializeFunctionCall_nextId c isLast outcome initial
    cases hr : outcome.returnData <;> simpa only [hr, immediateDataCount] using he
  rw [hn]
  rcases hm with hd | ha
  · obtain ⟨hl, hu⟩ := List.mem_range'_1.mp hd
    constructor
    · omega
    · exact hu
  · obtain ⟨hl, hu⟩ := List.mem_range'_1.mp ha
    constructor
    · exact hl
    · exact hu.trans_le ((Nat.le_add_right (initial.nextId + outcome.receipts.length)
        (outcome.receipts.map fun spec => spec.dependencies.length).sum).trans (Nat.le_add_right _ _))

/-- Every materialized envelope is fresh against all old routing references. -/
theorem materializeFunctionCall_receiptId_fresh (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (h : initial.IdsBelowNext) (receipt : Receipt)
    (hmem : receipt ∈ (materializeFunctionCall c isLast outcome initial).receipts) :
    receipt.receiptId ∉ initial.liveIds := by
  have hb := (materializeFunctionCall_receiptId_bounds c isLast outcome initial receipt hmem).1
  intro hold
  have := h receipt.receiptId hold
  omega

/-- Freshly materialized receipt ids have no postponed slot in the returned
state, so local conservation's non-overwrite premise follows from the frontier. -/
theorem materializeFunctionCall_postponed_fresh (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (h : initial.IdsBelowNext) (receipt : Receipt)
    (hmem : receipt ∈ (materializeFunctionCall c isLast outcome initial).receipts) :
    Assoc.lookup (materializeFunctionCall c isLast outcome initial).state.postponed receipt.receiptId = none := by
  have hf := congrArg (fun st => Assoc.lookup st.postponed receipt.receiptId)
    (materializeFunctionCall_frame c isLast outcome initial)
  change Assoc.lookup (materializeFunctionCall c isLast outcome initial).state.postponed receipt.receiptId =
    Assoc.lookup initial.postponed receipt.receiptId at hf
  rw [hf]
  exact h.postponed_lookup_none receipt.receiptId
    (materializeFunctionCall_receiptId_bounds c isLast outcome initial receipt hmem).1

end Near
