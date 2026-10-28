import Proofs.AllocationGrowthRemainder
import Proofs.AllocateRetryDomain

/-! Room for a second allocation is derived from the original block interval;
no read or native condition of the resulting heap is assumed. -/
namespace WNear.Proofs.AllocationGrowthRemainder
open Wasm Wasm.Near MeteredLogic

/-- Splitting consumes exactly the original request plus its eight-byte header. -/
theorem remainder_header_nat (p:AllocateSearch.Layout) (hn:AllocateFlagged.Native p) :
    (AllocateFlagged.header p).toNat =
      (AllocateFlagged.finish p).toNat-p.words.toNat*4-8 := by
  have pointer:=Allocate.split_pointer_toNat p.memory (AllocateFlagged.head p) p.words hn.split
  have header:=Allocate.split_header_toNat p.memory (AllocateFlagged.head p) p.words hn.split
  change (Allocate.splitHeader p.memory (AllocateFlagged.head p) p.words).toNat = (Allocate.endWord p.memory (AllocateFlagged.head p)).toNat-p.words.toNat*4-8
  rw[header,pointer]

/-- A stronger original block interval supplies the next split's full native room. -/
theorem next_split_native (p:AllocateSearch.Layout) (hn:AllocateFlagged.Native p)
    (words:UInt32) (positive:0<words.toNat)
    (room:(AllocateFlagged.head p).toNat+88+p.words.toNat*4+words.toNat*4≤
      (AllocateFlagged.finish p).toNat) :
    Allocate.SplitNative (AllocateFlagged.finalMemory p) (AllocateFlagged.head p) words := by
  have h:=remainder_header_nat p hn
  have interval:=AllocateFlagged.intervals p hn
  have shape:=AllocateFlagged.final_shape p hn
  refine ⟨positive,?_,?_⟩
  · rw[final_end p hn]
    omega
  · rw[final_end p hn,shape.size]
    omega

/-- In particular, an eight-word allocation in a full fresh page leaves room
for the one-word accounts-prefix allocation used by the decoder. -/
theorem next_one_word (p:AllocateSearch.Layout) (hn:AllocateFlagged.Native p)
    (words:p.words.toNat=8)
    (page:(AllocateFlagged.head p).toNat+65536≤(AllocateFlagged.finish p).toNat) :
    Allocate.SplitNative (AllocateFlagged.finalMemory p) (AllocateFlagged.head p) 1 := by
  apply next_split_native p hn 1 (by decide)
  have one:(1:UInt32).toNat=1:=rfl
  rw[words,one]
  omega
end WNear.Proofs.AllocationGrowthRemainder
