import Proofs.AllocateVectorOuterMemory
import Proofs.AllocateVectorRecordReadback
import Proofs.AllocateVectorOuterOutputReadback

/-! All three687 output words follow from the cached686 record, with no
source/destination separation assumption. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] finalMemory allocatedMemory cacheWord readI32 readI64

theorem final_record (p : Layout) (hn : Native p) :
    readI32 (finalMemory p) p.out687.toNat=AllocateVector.result p.toVector ∧
    readI32 (finalMemory p) (p.out687.toNat+4)=p.size ∧
    readI32 (finalMemory p) (p.out687.toNat+8)=p.size := by
  have shape := allocated_spec p hn
  have bound := hn.outputBound.trans shape.2.1
  have inner := AllocateVector.final_words p.toVector (hn.vector p)
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have address : p.out686.toNat=p.outerSP.toNat+8 := by rw [nums.1,nums.2.2];omega
  have low : readI32 (allocatedMemory p) (p.outerSP.toNat+8)=AllocateVector.result p.toVector := by
    simpa only [allocatedMemory,address] using inner.1
  have high : readI32 (allocatedMemory p) (p.outerSP.toNat+8+4)=p.size := by
    simpa only [allocatedMemory,address] using inner.2
  have words := outputMemory_words_of_snapshot (allocatedMemory p) p.out687 p.size (p.outerSP.toNat+8) shape.1 bound
  have length := (final_spec p hn).2.2.2.2
  refine ⟨?_,?_,length⟩
  · simpa only [finalMemory,cacheWord] using words.1.trans low
  · simpa only [finalMemory,cacheWord] using words.2.trans high
end WNear.Proofs.AllocateVectorOuter
