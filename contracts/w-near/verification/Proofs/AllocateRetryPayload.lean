import Proofs.AllocateRetryDomain
import Proofs.AllocateFlaggedPayload

/-! Original growth-and-retry data bound the actual allocation payload. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem requested_le_words (p : Layout) (hn : Native p) : p.size.toNat≤(words p).toNat*4 := by
  have h := DeallocateAlign.quotient570_toNat p.size hn.rounding
  change (words p).toNat=(p.size.toNat+3)/4 at h
  omega

/-- Both actual relink writes retain the memory extent produced by growth. -/
theorem secondMemory_spec (p : Layout) (hn : Native p) :
    (secondLayout p).memory.wf ∧
    (secondLayout p).memory.byteSize=p.memory.byteSize+(AllocateGrowth.delta (growthLayout p)).toNat*65536 ∧
    (secondLayout p).memory.max=p.memory.max := by
  have saved := saved_shape p hn
  have bounds := scratch_numbers p hn
  have growth := AllocateGrowth.finalMemory_spec (growthLayout p) hn.growth
  have grown := hn.growth.grown_spec (growthLayout p)
  have record : (growthLayout p).record.toNat+16≤(AllocateGrowth.finalMemory (growthLayout p)).byteSize := by
    rw [growth.2.1]
    change (scratch p).toNat+16≤(savedMemory p).byteSize+_
    rw [saved.2.1]
    omega
  have header : (AllocateGrowth.header (growthLayout p)).toNat+12≤(AllocateGrowth.finalMemory (growthLayout p)).byteSize := by
    rw [growth.2.1,←grown.2.1]
    exact grown.2.2.1
  have linked := relink_spec (AllocateGrowth.finalMemory (growthLayout p)) (growthLayout p).record
    (AllocateGrowth.header (growthLayout p)) growth.1 record header
  have memSize := linked.2.1.trans growth.2.1
  have finalSize : (secondLayout p).memory.byteSize=p.memory.byteSize+(AllocateGrowth.delta (growthLayout p)).toNat*65536 := by
    change (relinkMemory (AllocateGrowth.finalMemory (growthLayout p)) (growthLayout p).record _).byteSize=_
    rw [memSize]
    exact congrArg (fun n=>n+(AllocateGrowth.delta (growthLayout p)).toNat*65536) saved.2.1
  exact ⟨linked.1,finalSize,linked.2.2.1.trans (growth.2.2.trans saved.2.2)⟩

theorem searchedMemory_spec (p : Layout) (hn : Native p) :
    (searchedMemory p).wf ∧
    (searchedMemory p).byteSize=p.memory.byteSize+(AllocateGrowth.delta (growthLayout p)).toNat*65536 ∧
    (searchedMemory p).max=p.memory.max := by
  have original := secondMemory_spec p hn
  have split := AllocateFlagged.final_shape (secondLayout p) (native_second p hn)
  exact ⟨split.wf,split.size.trans original.2.1,split.max.trans original.2.2⟩

/-- The final allocator-head update preserves the full grown memory extent. -/
theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧
    (finalMemory p).byteSize=p.memory.byteSize+(AllocateGrowth.delta (growthLayout p)).toNat*65536 ∧
    (finalMemory p).max=p.memory.max := by
  have search := searchedMemory_spec p hn
  have bound : p.allocator.toNat+4≤(searchedMemory p).byteSize := by rw [search.2.1];have:=hn.allocatorBound;omega
  have final := writeI32_spec (searchedMemory p) p.allocator.toNat
    (readI32 (searchedMemory p) ((scratch p).toNat+12)) search.1 bound
  exact ⟨final.1,final.2.1.trans search.2.1,final.2.2.1.trans search.2.2⟩

theorem result_nonzero_and_span (p : Layout) (hn : Native p) :
    result p≠0 ∧ (result p).toNat+(words p).toNat*4≤(finalMemory p).byteSize := by
  have span := AllocateFlagged.pointer_nonzero_and_span (secondLayout p) (native_second p hn)
  have search := searchedMemory_spec p hn
  have final := finalMemory_spec p hn
  have eq : (AllocateFlagged.finalMemory (secondLayout p)).byteSize=(finalMemory p).byteSize := search.2.1.trans final.2.1.symm
  exact ⟨span.1,span.2.trans_eq eq⟩

theorem result_size_span (p : Layout) (hn : Native p) : (result p).toNat+p.size.toNat≤(finalMemory p).byteSize := by
  have span := (result_nonzero_and_span p hn).2
  have rounded := requested_le_words p hn
  omega

theorem result_width (p : Layout) (hn : Native p) : (result p).toNat+p.size.toNat≤2^32 := by
  have span := result_size_span p hn
  have pages := hn.pagesBound
  rw [(finalMemory_spec p hn).2.1] at span
  change (result p).toNat+p.size.toNat≤_
  have bytes : p.memory.byteSize=p.memory.size*65536 := rfl
  rw [bytes] at span
  omega
end WNear.Proofs.AllocateRetry
