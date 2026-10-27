import Proofs.AllocatePositiveResult

/-! Original allocation conditions bound the exact requested payload for zero-fill. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem requested_le_words (p : Layout) (hn : Native p) : p.size.toNat≤(words p).toNat*4 := by
  have h := DeallocateAlign.quotient570_toNat p.size hn.rounding
  change (words p).toNat=(p.size.toNat+3)/4 at h
  omega

theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧ (finalMemory p).max=p.memory.max := by
  have bounds := scratch_numbers p hn
  have saved := writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hn.wf (by omega)
  have search := AllocateSearch.final_shape (searchLayout p) hn.search
  have size : (searchedMemory p).byteSize=p.memory.byteSize := search.size.trans saved.2.1
  have maximum : (searchedMemory p).max=p.memory.max := search.max.trans saved.2.2.1
  have bound : p.allocator.toNat+4≤(searchedMemory p).byteSize := by rw [size];exact hn.allocatorBound
  have final := writeI32_spec (searchedMemory p) p.allocator.toNat
    (readI32 (searchedMemory p) ((scratch p).toNat+12)) search.wf bound
  exact ⟨final.1,final.2.1.trans size,final.2.2.1.trans maximum⟩

theorem result_size_span (p : Layout) (hn : Native p) :
    (result p).toNat+p.size.toNat≤(finalMemory p).byteSize := by
  have span := (result_nonzero_and_span p hn).2
  have wordsBound := requested_le_words p hn
  rw [(finalMemory_spec p hn).2.1]
  omega

theorem result_width (p : Layout) (hn : Native p) : (result p).toNat+p.size.toNat≤2^32 := by
  have span := result_size_span p hn
  rw [(finalMemory_spec p hn).2.1] at span
  exact span.trans hn.width

end WNear.Proofs.AllocatePositive
