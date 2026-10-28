import Proofs.StateReadRegisterOuterLengthMemory
import Proofs.AllocateSetupGrowthCanonical

/-! The actual f687 allocation domain follows from original f523 resources and
the proved length-query footprint. Growth is reconstructed on its actual memory. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 lengthMemory vectorSaved vectorGrown
  StateDispatchLength.finalMemory StateDispatchLength.lowMemory StateDispatchLengthOuterTail.finalMemory

theorem vectorSaved_spec (p : Layout) (hn : Native p) :
    (vectorSaved p).wf ∧ (vectorSaved p).byteSize=p.memory.byteSize ∧
    (vectorSaved p).max=p.memory.max ∧ (vectorSaved p).size=p.memory.size := by
  have shape := lengthMemory_footprint p hn
  have original := hn.vector_original p
  have nums := AllocateVector.stack_numbers p.toVector original.vector
  have low := original.vector.spLower
  have bound := original.vector.spBound
  have hb : (p.sp-16).toNat+12+4≤(lengthMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.1];omega
  have sv := writeI32_spec (lengthMemory p) ((p.sp-16).toNat+12)
    (readI32 (lengthMemory p) p.allocator.toNat) shape.1 hb
  have eq : vectorSaved p=writeI32 (lengthMemory p) ((p.sp-16).toNat+12)
      (readI32 (lengthMemory p) p.allocator.toNat) := by
    unfold vectorSaved
    rfl
  have bytes : (vectorSaved p).byteSize=p.memory.byteSize := by rw [eq,sv.2.1,shape.2.1]
  have size : (vectorSaved p).size=p.memory.size := by
    change (vectorSaved p).size*65536=p.memory.size*65536 at bytes
    omega
  exact ⟨by rw [eq];exact sv.1,bytes,by rw [eq,sv.2.2.1,shape.2.2.1],size⟩

theorem vector_grow (p : Layout) (hn : Native p) :
    (vectorSaved p).grow (vectorDelta p).toNat=some (vectorGrown p) := by
  have target := vectorSaved_spec p hn
  have source := AllocateRetry.saved_shape p.toRetry hn.allocation
  have sourceSize := AllocateRetry.saved_size p.toRetry hn.allocation
  have hg := hn.allocation.growth.grow
  have hs : (vectorSaved p).size=(AllocateRetry.savedMemory p.toRetry).size := target.2.2.2.trans sourceSize.symm
  have hm : (vectorSaved p).max=(AllocateRetry.savedMemory p.toRetry).max := target.2.2.1.trans source.2.2.symm
  have result := AllocateSetupGrowth.grow_eq_of_shape _ (vectorSaved p) p.grown (vectorDelta p).toNat hs hm hg
  simpa only [vectorGrown,AllocateSetupGrowth.grownMemory] using result

theorem vector_growth_native (p : Layout) (hn : Native p) :
    AllocateGrowth.Native (AllocateRetry.growthLayout (actualVector p).toRetry) := by
  let q := AllocateRetry.growthLayout (actualVector p).toRetry
  have old := hn.allocation.growth
  have target := vectorSaved_spec p hn
  have nums := AllocateVector.stack_numbers p.toVector (hn.vector_original p).vector
  have low := (hn.vector_original p).vector.spLower
  have bound := (hn.vector_original p).vector.spBound
  have memoryEq : q.memory=vectorSaved p := by
    simp only [q,AllocateRetry.growthLayout,AllocateRetry.savedMemory,AllocatePositive.savedMemory,
      AllocatePositive.scratch,actualVector,vectorMemoryTemplate,vectorSaved]
  have deltaEq : AllocateGrowth.delta q=vectorDelta p := rfl
  have sizeEq : q.memory.size=p.memory.size := by rw [memoryEq];exact target.2.2.2
  have wf : q.memory.wf := by rw [memoryEq];exact target.1
  have grownEq : q.grown=vectorGrown p := rfl
  have grow : q.memory.grow (AllocateGrowth.delta q).toNat=some q.grown := by
    rw [memoryEq,deltaEq,grownEq]
    exact vector_grow p hn
  have recordBound : q.record.toNat+8≤q.memory.byteSize := by
    rw [memoryEq,target.2.1]
    change (p.sp-16).toNat+8≤p.memory.byteSize
    rw [nums.2.2.2.2.1];omega
  refine ⟨old.wordsBound,old.alignAdd,old.alignMask,old.padAdd,old.roundBound,
    old.pagesBound,old.pagesPositive,?_,wf,grow,recordBound⟩
  rw [sizeEq]
  have source := AllocateRetry.saved_size p.toRetry hn.allocation
  have h := old.oldPagesBound
  change (AllocateRetry.savedMemory p.toRetry).size<65536 at h
  rw [source] at h
  exact h

theorem vector_native (p : Layout) (hn : Native p) (haRoot : p.allocator=1074896) : AllocateVectorOuter.Native (actualVector p) := by
  have original := hn.vector_original p
  have shape := lengthMemory_footprint p hn
  have low := hn.spLower
  have bound := hn.spBound
  have heap := hn.heapAbove
  have nums := stack_numbers p hn
  have empty := (lengthMemory_word p hn p.allocator.toNat heap
    (by left;rw [haRoot];decide)).trans hn.allocation.empty
  have allocatorBound : p.allocator.toNat+4≤(lengthMemory p).byteSize := by rw [shape.2.1];exact hn.allocation.allocatorBound
  have width : (lengthMemory p).byteSize≤2^32 := by rw [shape.2.1];exact hn.allocation.width
  have spBound : p.sp.toNat≤(lengthMemory p).byteSize := by rw [shape.2.1];exact hn.allocation.spBound
  have oldPositive : 0<(lengthMemory p).size := by rw [lengthMemory_size p hn];exact hn.allocation.oldPositive
  have pages : (lengthMemory p).size+(vectorDelta p).toNat<65536 := by rw [lengthMemory_size p hn];exact hn.allocation.pagesBound
  have vt : 1057464+20≤(lengthMemory p).byteSize := by rw [shape.2.1];exact hn.allocation.vtableBound
  have child : AllocateZeroedRetry.Native (actualVector p).toZeroed :=
    ⟨hn.allocation.positive,hn.allocation.rounding,shape.1,width,hn.allocation.spLower,spBound,
      allocatorBound,empty,vector_growth_native p hn,oldPositive,pages,hn.allocation.wordsPositive,
      hn.allocation.room,vt,hn.allocation.callbackSep⟩
  exact ⟨child,original.innerSP,original.childSP,original.childOut,original.outerGlobal,
    original.childGlobal,original.innerOut,original.spLower,
    by change p.sp687.toNat≤(lengthMemory p).byteSize;rw [shape.2.1];exact original.spBound,
    original.sizeBound,
    by change p.out687.toNat+12≤(lengthMemory p).byteSize;rw [shape.2.1];exact original.outputBound,
    original.heapAbove,original.callbackAbove,original.byteFlag⟩
end WNear.Proofs.StateReadRegisterOuter
