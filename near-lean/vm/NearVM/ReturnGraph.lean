import NearVM.ReturnSelection

namespace Wasm.Near

/-- Conversion only appends handles; earlier identities remain stable. -/
theorem ConvertsPromise.preserves_lookup {g next : PromiseGraph} {p : NearPromise}
    (h : ConvertsPromise g p next) {index : Nat} {handle : PromiseHandle}
    (lookup : g.handles[index]? = some handle) : next.handles[index]? = some handle := by
  cases h <;> dsimp only [PromiseGraph.addReceipt, PromiseGraph.addJoint]
  all_goals rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).1]; exact lookup

theorem ConvertsPromises.preserves_lookup {g result : PromiseGraph} {ps : List NearPromise}
    (h : ConvertsPromises g ps result) {index : Nat} {handle : PromiseHandle}
    (lookup : g.handles[index]? = some handle) : result.handles[index]? = some handle := by
  induction h with
  | nil => exact lookup
  | cons head tail ih => exact ih (head.preserves_lookup lookup)

theorem ConvertsPromise.new_receipt {g next : PromiseGraph} {p : NearPromise}
    (h : ConvertsPromise g p next) (hp : p.NonJoint) :
    ∃ receipt, next.handles[g.handles.length]? = some (.receipt receipt) := by
  cases h with
  | batch => exact ⟨g.receipts.length, by simp [PromiseGraph.addReceipt]⟩
  | callback => exact ⟨g.receipts.length, by simp [PromiseGraph.addReceipt]⟩
  | yielded => exact ⟨g.receipts.length, by simp [PromiseGraph.addReceipt]⟩
  | joint => cases hp

/-- A non-joint raw handle converts to a receipt at the same handle slot,
even when further receipts and nested joins follow it. -/
theorem ConvertsPromises.selected_receipt {g result : PromiseGraph} {ps : List NearPromise}
    (h : ConvertsPromises g ps result) {index : Nat} {p : NearPromise}
    (lookup : getPromise? ps index = some p) (hp : p.NonJoint) :
    ∃ receipt, result.handles[g.handles.length + index]? = some (.receipt receipt) := by
  induction h generalizing index with
  | nil => simp [getPromise?] at lookup
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [getPromise?, Option.some.injEq] at lookup
      subst p
      obtain ⟨receipt, hreceipt⟩ := head.new_receipt hp
      exact ⟨receipt, tail.preserves_lookup hreceipt⟩
    | succ index =>
      have htail : getPromise? _ index = some p := lookup
      obtain ⟨receipt, hreceipt⟩ := ih htail
      refine ⟨receipt, ?_⟩
      simpa only [head.handles_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreceipt

/-- Valid selection cannot disappear or turn into a joint during conversion. -/
theorem convertPromises_return_selection {ns : NearState} {graph : PromiseGraph}
    (hconvert : convertPromises ns.promises = some graph) (hselection : ReturnSelectionValid ns)
    {index : Nat} (hreturn : ns.returnedPromise = some index) :
    ∃ receipt, graph.returnedReceipt? index = some receipt ∧ receipt < graph.receipts.length := by
  obtain ⟨p, hget, hsingle⟩ := hselection index hreturn
  obtain ⟨receipt, hreceipt⟩ := ((convertPromises_iff _ _).mp hconvert).selected_receipt hget hsingle
  have hlookup : graph.handles[index]? = some (.receipt receipt) := by simpa using hreceipt
  have hreturned : graph.returnedReceipt? index = some receipt := by
    simp only [PromiseGraph.returnedReceipt?, hlookup]
  exact ⟨receipt, hreturned, PromiseGraph.returnedReceipt_lt (convertPromises_valid hconvert) hreturned⟩

theorem PromiseGraph.returnData?_total {ns : NearState} {graph : PromiseGraph}
    (hconvert : convertPromises ns.promises = some graph) (hselection : ReturnSelectionValid ns) :
    ∃ data, graph.returnData? ns = some data := by
  cases hreturn : ns.returnedPromise with
  | none => exact ⟨match ns.returnData with | some bytes => .value bytes | none => .none,
      by simp only [returnData?, hreturn]; rfl⟩
  | some index =>
    obtain ⟨receipt, hreceipt, hbound⟩ := convertPromises_return_selection hconvert hselection hreturn
    exact ⟨.receiptIndex receipt, by simp only [returnData?, hreturn, hreceipt, Option.map_some]⟩

end Wasm.Near
