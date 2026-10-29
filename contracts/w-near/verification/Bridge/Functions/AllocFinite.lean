import Bridge.Functions.AllocInv

/-!
# A uniform finite bound for the allocator's free list

A returned existential free-list bound need not be related to its caller's bound.
The heap geometry nevertheless bounds the actual distinct free-cell addresses by
its byte length. This gives error-only continuations a fixed finite allocation
cost without changing the accepting parser's tighter cost contracts.
-/

namespace WNear.Binary.AllocInv

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI

/-- Every listed free-cell address lies within the heap's memory length. -/
theorem HeapModel.wf.freeList_length_le {H : HeapModel} {live : List (Nat × Nat)} {F : Nat}
    (hw : H.wf live F) : H.freeList.length ≤ H.len := by
  have hsub : H.freeList ⊆ List.range H.len := by
    intro a ha
    obtain ⟨c, hc, _⟩ := hw.lists.fl_free a ha
    have hm : c ∈ H.cells := List.mem_of_find?_eq_some hc
    have he : c.addr = a := by simpa only [HeapModel.cellAt, beq_iff_eq] using List.find?_some hc
    have hb := hw.geo.bounds c hm
    apply List.mem_range.mpr
    omega
  have hlen := hw.lists.fl_nodup.length_le_of_subset hsub
  simpa only [List.length_range] using hlen

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Any valid heap can use the fixed `2^32` free-list bound. -/
theorem heapInv_finite (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) :
    heapInv (GF := GF) n maxP len live F ⊢ heapInv n maxP len live (2 ^ 32) := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hw, hlen⟩, Hh, Hl, Hm, Hc⟩
  have hb : M.freeList.length ≤ 2 ^ 32 := by
    have := hw.freeList_length_le
    have := hw.len_lt
    omega
  iunfold heapInv
  iexists M
  isplitr
  · ipureintro
    exact ⟨{ hw with lists := { hw.lists with fl_len := hb } }, hlen⟩
  iframe Hh Hl Hm Hc

end Proof

end WNear.Binary.AllocInv
