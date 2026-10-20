import NearRuntime.ActionReceiptIdentifiers

namespace Near
open Wasm.Near

/-- Pointwise array predicates survive modification when the update preserves
that predicate. Out-of-range modification needs no special validity premise. -/
theorem array_modify_forall (values : Array α) (P : α → Prop) (index : Nat) (update : α → α)
    (h : ∀ i (hi : i < values.size), P values[i])
    (hupdate : ∀ value, P value → P (update value)) :
    ∀ i (hi : i < (values.modify index update).size), P (values.modify index update)[i] := by
  intro i hi
  rw [Array.getElem_modify]
  split
  · exact hupdate _ (h i (by simpa using hi))
  · exact h i (by simpa using hi)

def OutputDataIdsBelow (bound : Nat) (outputs : Array (List DataReceiver)) : Prop :=
  ∀ i (hi : i < outputs.size), ∀ output ∈ outputs[i], output.dataId < bound

def InputDataIdsBelow (bound : Nat) (inputs : Array (List DataId)) : Prop :=
  ∀ i (hi : i < inputs.size), ∀ id ∈ inputs[i], id < bound

/-- Each dependency consumes a fresh data identity and places references below
the resulting counter. This bound is independent of edge-index validity. -/
theorem linkFunctionCallDependencies_bounds (specs : List ReceiptSpec) (initial : ChainState)
    (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (hout : OutputDataIdsBelow initial.nextId outputs)
    (hin : InputDataIdsBelow initial.nextId inputs) :
    OutputDataIdsBelow (linkFunctionCallDependencies specs initial outputs inputs).1.nextId
      (linkFunctionCallDependencies specs initial outputs inputs).2.1 ∧
    InputDataIdsBelow (linkFunctionCallDependencies specs initial outputs inputs).1.nextId
      (linkFunctionCallDependencies specs initial outputs inputs).2.2 := by
  simp only [linkFunctionCallDependencies, ChainState.freshId, List.forIn_pure_yield_eq_foldl,
    pure_bind, Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl]
  apply foldl_preserves (fun triple : ChainState × Array (List DataReceiver) × Array (List DataId) =>
    OutputDataIdsBelow triple.1.nextId triple.2.1 ∧ InputDataIdsBelow triple.1.nextId triple.2.2)
  · intro triple item htriple
    apply foldl_preserves (fun triple : ChainState × Array (List DataReceiver) × Array (List DataId) =>
      OutputDataIdsBelow triple.1.nextId triple.2.1 ∧ InputDataIdsBelow triple.1.nextId triple.2.2) _ _ _ _ htriple
    intro current dep hcurrent
    constructor
    · dsimp only [OutputDataIdsBelow]
      apply array_modify_forall _ (fun entries : List DataReceiver =>
        ∀ output ∈ entries, output.dataId < current.1.nextId + 1)
      · intro i hi output hmem
        exact (hcurrent.1 i hi output hmem).trans (Nat.lt_succ_self _)
      · intro entries hentries output hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hold | rfl
        · exact hentries output hold
        · exact Nat.lt_succ_self _
    · dsimp only [InputDataIdsBelow]
      apply array_modify_forall _ (fun entries : List DataId =>
        ∀ id ∈ entries, id < current.1.nextId + 1)
      · intro i hi id hmem
        exact (hcurrent.2 i hi id hmem).trans (Nat.lt_succ_self _)
      · intro entries hentries id hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hold | rfl
        · exact hentries id hold
        · exact Nat.lt_succ_self _
  · exact ⟨hout, hin⟩

/-- The actual materializer starts dependency linking with empty reference
arrays, so its local data-id bounds need no caller-supplied array invariant. -/
theorem linkFunctionCallDependencies_empty_bounds (specs : List ReceiptSpec) (initial : ChainState) :
    let linked := linkFunctionCallDependencies specs initial
      (Array.replicate specs.length []) (Array.replicate specs.length [])
    OutputDataIdsBelow linked.1.nextId linked.2.1 ∧ InputDataIdsBelow linked.1.nextId linked.2.2 := by
  apply linkFunctionCallDependencies_bounds
  · simp [OutputDataIdsBelow]
  · simp [InputDataIdsBelow]

theorem array_getD_forall (values : Array α) (P : α → Prop) (index : Nat) (fallback : α)
    (h : ∀ i (hi : i < values.size), P values[i]) (hdefault : P fallback) :
    P (values[index]?.getD fallback) := by
  by_cases hi : index < values.size
  · simpa [hi] using h index hi
  · simpa [hi] using hdefault

/-- Action emission preserves the bound for every carried reference, including
input and output data ids, not just its receipt envelope identity. -/
theorem emitFunctionCallActions_liveIds_below (c : ReceiptCtx) (specs : List ReceiptSpec)
    (ids : Array ReceiptId) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (receipts : List Receipt) (bound : Nat) (hsize : ids.size = specs.length)
    (hids : ∀ i (hi : i < ids.size), ids[i] < bound)
    (hout : OutputDataIdsBelow bound outputs) (hin : InputDataIdsBelow bound inputs)
    (hreceipts : ∀ receipt ∈ receipts, ∀ id ∈ receipt.liveIds, id < bound) :
    ∀ receipt ∈ emitFunctionCallActions c specs ids outputs inputs receipts,
      ∀ id ∈ receipt.liveIds, id < bound := by
  simp only [emitFunctionCallActions, Std.Legacy.Range.forIn'_eq_forIn'_range',
    List.forIn'_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply foldl_preserves (fun receipts : List Receipt => ∀ receipt ∈ receipts, ∀ id ∈ receipt.liveIds, id < bound)
  · intro receipts item hbefore receipt hmem id hid
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hold | rfl
    · exact hbefore receipt hold id hid
    · have hi : item.val < ids.size := by
        have hr := List.mem_range'_1.mp item.property
        omega
      have hinput := array_getD_forall inputs (fun entries => ∀ id ∈ entries, id < bound) item.val [] hin
        (by simp)
      have houtput := array_getD_forall outputs (fun entries => ∀ output ∈ entries, output.dataId < bound) item.val [] hout
        (by simp)
      simp only [Receipt.liveIds, List.mem_cons, List.mem_append] at hid
      rcases hid with he | hinmem | houtmem
      · rw [he]
        simpa [hi] using hids item.val hi
      · exact hinput id hinmem
      · obtain ⟨output, hmem, he⟩ := List.mem_map.mp houtmem
        rw [← he]
        exact houtput output hmem
  · exact hreceipts

theorem OutputDataIdsBelow.mono {before after : Nat} {outputs : Array (List DataReceiver)}
    (h : OutputDataIdsBelow before outputs) (hle : before ≤ after) : OutputDataIdsBelow after outputs := by
  intro i hi output hm
  exact (h i hi output hm).trans_le hle

theorem InputDataIdsBelow.mono {before after : Nat} {inputs : Array (List DataId)}
    (h : InputDataIdsBelow before inputs) (hle : before ≤ after) : InputDataIdsBelow after inputs := by
  intro i hi id hm
  exact (h i hi id hm).trans_le hle

/-- Composition of the two real emission passes for a direct return. -/
theorem emitFunctionCall_directReturn_liveIds_below (c : ReceiptCtx) (specs : List ReceiptSpec)
    (ids : Array ReceiptId) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (initial : ChainState) (bytes : Bytes) (receivers : List DataReceiver)
    (hsize : ids.size = specs.length) (hids : ∀ i (hi : i < ids.size), ids[i] < initial.nextId)
    (hout : OutputDataIdsBelow initial.nextId outputs) (hin : InputDataIdsBelow initial.nextId inputs)
    (hreceivers : ∀ receiver ∈ receivers, receiver.dataId < initial.nextId) :
    let emitted := emitFunctionCallData c.receipt.receiverId bytes receivers initial
    ∀ receipt ∈ emitFunctionCallActions c specs ids outputs inputs emitted.2,
      ∀ id ∈ receipt.liveIds, id < emitted.1.nextId := by
  have hle : initial.nextId ≤ (emitFunctionCallData c.receipt.receiverId bytes receivers initial).1.nextId := by
    rw [emitFunctionCallData_nextId]
    exact Nat.le_add_right _ _
  apply emitFunctionCallActions_liveIds_below _ _ _ _ _ _ _ hsize
  · intro i hi
    exact (hids i hi).trans_le hle
  · exact hout.mono hle
  · exact hin.mono hle
  · exact emitFunctionCallData_liveIds_below _ _ _ _ [] (by simp) hreceivers

/-- All identifiers in the complete materializer's output lie below its final
counter. Only inherited callback references need a caller-supplied bound; newly
allocated dependency references are proved bounded from the actual loops. -/
theorem materializeFunctionCall_liveIds_below (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState)
    (_hinherited : ∀ receiver ∈ c.action.outputDataReceivers, receiver.dataId < initial.nextId) :
    ∀ receipt ∈ (materializeFunctionCallRaw c isLast outcome initial).receipts,
      ∀ id ∈ receipt.liveIds, id < (materializeFunctionCallRaw c isLast outcome initial).state.nextId := by
  let allocation := allocateFunctionCallIds outcome.receipts initial
  let linked := linkFunctionCallDependencies outcome.receipts allocation.1
    (Array.replicate outcome.receipts.length []) (Array.replicate outcome.receipts.length [])
  have hsize : allocation.2.size = outcome.receipts.length := by
    have hl := congrArg List.length (allocateFunctionCallIds_ids outcome.receipts initial #[])
    simpa using hl
  have hle : allocation.1.nextId ≤ linked.1.nextId := by
    dsimp only [linked]
    rw [linkFunctionCallDependencies_nextId]
    exact Nat.le_add_right _ _
  have hinitial : initial.nextId ≤ linked.1.nextId := by
    apply Nat.le_trans _ hle
    dsimp only [allocation]
    rw [allocateFunctionCallIds_nextId]
    exact Nat.le_add_right _ _
  have hids : ∀ i (hi : i < allocation.2.size), allocation.2[i] < linked.1.nextId := by
    intro i hi
    exact (allocateFunctionCallIds_bounds outcome.receipts initial _ (Array.getElem_mem_toList hi)).2.trans_le hle
  have hlinked : OutputDataIdsBelow linked.1.nextId linked.2.1 ∧ InputDataIdsBelow linked.1.nextId linked.2.2 :=
    linkFunctionCallDependencies_empty_bounds outcome.receipts allocation.1
  have hreceivers : ∀ receiver ∈ ([] : List DataReceiver), receiver.dataId < linked.1.nextId := by simp
  rw [materializeFunctionCallRaw_eq_stages]
  cases hr : outcome.returnData with
  | receiptIndex k =>
    dsimp only
    apply emitFunctionCallActions_liveIds_below _ _ _ _ _ _ _ hsize hids
    · dsimp only [OutputDataIdsBelow]
      apply array_modify_forall _ (fun entries : List DataReceiver => ∀ output ∈ entries, output.dataId < linked.1.nextId)
      · exact hlinked.1
      · intro entries hentries output hm
        simp only [List.mem_append] at hm
        rcases hm with hold | hnew
        · exact hentries output hold
        · exact hreceivers output hnew
    · exact hlinked.2
    · simp
  | value bytes =>
    dsimp only
    exact emitFunctionCallActions_liveIds_below _ _ _ _ _ _ _ hsize hids hlinked.1 hlinked.2 (by simp)
  | none =>
    dsimp only
    exact emitFunctionCallActions_liveIds_below _ _ _ _ _ _ _ hsize hids hlinked.1 hlinked.2 (by simp)

/-- The inherited-reference premise follows from the ordinary incoming receipt
bound and the context's agreement with that receipt's action payload. -/
theorem materializeFunctionCall_liveIds_below_of_receipt (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (hreceipt : c.receipt.receipt = .action c.action)
    (hbound : ∀ id ∈ c.receipt.liveIds, id < initial.nextId) :
    ∀ receipt ∈ (materializeFunctionCallRaw c isLast outcome initial).receipts,
      ∀ id ∈ receipt.liveIds, id < (materializeFunctionCallRaw c isLast outcome initial).state.nextId := by
  apply materializeFunctionCall_liveIds_below
  intro receiver hm
  apply hbound
  simp only [Receipt.liveIds, hreceipt, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (List.mem_map.mpr ⟨receiver, hm, rfl⟩))

end Near
