import Proofs.AllocateVectorOuterPhases
import Proofs.AllocateVectorResources

/-! The687 callee's memory shape and the cached output snapshot follow from
original native bounds, retaining arbitrary output/source aliases. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 allocatedMemory AllocateVector.finalMemory AllocateVector.resultMemory

theorem allocated_spec (p : Layout) (hn : Native p) :
    (allocatedMemory p).wf ∧ p.memory.byteSize≤(allocatedMemory p).byteSize ∧
    (allocatedMemory p).max=p.memory.max := by
  have inner := hn.vector p
  have shape := AllocateVector.resultMemory_spec p.toVector inner
  have bound : p.out686.toNat+8≤(AllocateVector.resultMemory p.toVector).byteSize :=
    inner.outputBound.trans shape.2.1
  have a := writeI32_spec (AllocateVector.resultMemory p.toVector) p.out686.toNat (AllocateVector.result p.toVector) shape.1 (by omega)
  have highBound : p.out686.toNat+4+4≤(writeI32 (AllocateVector.resultMemory p.toVector) p.out686.toNat (AllocateVector.result p.toVector)).byteSize := by
    rw [a.2.1];omega
  have b := writeI32_spec (writeI32 (AllocateVector.resultMemory p.toVector) p.out686.toNat (AllocateVector.result p.toVector))
    (p.out686.toNat+4) p.size a.1 highBound
  have wf : (allocatedMemory p).wf := by
    simpa only [allocatedMemory,AllocateVector.finalMemory,AllocateVector.recordMemory] using b.1
  have bytes : (allocatedMemory p).byteSize=(AllocateVector.resultMemory p.toVector).byteSize := by
    simpa only [allocatedMemory,AllocateVector.finalMemory,AllocateVector.recordMemory] using b.2.1.trans a.2.1
  have maxEq : (allocatedMemory p).max=(AllocateVector.resultMemory p.toVector).max := by
    simpa only [allocatedMemory,AllocateVector.finalMemory,AllocateVector.recordMemory] using b.2.2.1.trans a.2.2.1
  exact ⟨wf,by rw [bytes];exact shape.2.1,maxEq.trans shape.2.2⟩

theorem final_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ p.memory.byteSize≤(finalMemory p).byteSize ∧
    (finalMemory p).max=p.memory.max ∧
    readI64 (finalMemory p) p.out687.toNat=cacheWord p ∧
    readI32 (finalMemory p) (p.out687.toNat+8)=p.size := by
  have shape := allocated_spec p hn
  have outputBound := hn.outputBound.trans shape.2.1
  have output := outputMemory_spec (allocatedMemory p) p.out687 p.size (cacheWord p) shape.1 outputBound
  unfold finalMemory
  exact ⟨output.1,by rw [output.2.1];exact shape.2.1,
    output.2.2.1.trans shape.2.2,output.2.2.2.1,output.2.2.2.2.1⟩
end WNear.Proofs.AllocateVectorOuter
