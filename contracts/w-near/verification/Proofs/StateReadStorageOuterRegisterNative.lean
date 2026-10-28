import Proofs.StateReadStorageOuterCounter
import Proofs.StateReadRegisterOuterVectorNative

/-! Actual523 allocation/native data are reconstructed after459 from original548
native data and exact memory shape/static-word frames. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 storageMemory registerSaved

def registerGrown (p : Layout) := AllocateSetupGrowth.grownMemory (registerSaved p) (registerDelta p).toNat
theorem registerSaved_spec (p : Layout) (hn : Native p) :
    (registerSaved p).wf ∧ (registerSaved p).byteSize=p.memory.byteSize ∧
    (registerSaved p).max=p.memory.max ∧ (registerSaved p).size=p.memory.size := by
  have shape := storageMemory_footprint p hn
  have original := hn.register.vector_original p.toRegisterOuter
  have nums := AllocateVector.stack_numbers p.toVector original.vector
  have low := original.vector.spLower
  have bound := original.vector.spBound
  have hb : (p.sp-16).toNat+12+4≤(storageMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.1];omega
  have sv := writeI32_spec (storageMemory p) ((p.sp-16).toNat+12)
    (readI32 (storageMemory p) p.allocator.toNat) shape.1 hb
  have eq : registerSaved p=writeI32 (storageMemory p) ((p.sp-16).toNat+12)
      (readI32 (storageMemory p) p.allocator.toNat) := by
    unfold registerSaved
    rfl
  have bytes : (registerSaved p).byteSize=p.memory.byteSize := by rw [eq,sv.2.1,shape.2.1]
  have size : (registerSaved p).size=p.memory.size := by
    change (registerSaved p).size*65536=p.memory.size*65536 at bytes
    omega
  exact ⟨by rw [eq];exact sv.1,bytes,by rw [eq,sv.2.2.1,shape.2.2.1],size⟩

theorem register_grow (p : Layout) (hn : Native p) :
    (registerSaved p).grow (registerDelta p).toNat=some (registerGrown p) := by
  have target := registerSaved_spec p hn
  have source := AllocateRetry.saved_shape p.toRetry hn.register.allocation
  have sourceSize := AllocateRetry.saved_size p.toRetry hn.register.allocation
  have hg := hn.register.allocation.growth.grow
  have hs : (registerSaved p).size=(AllocateRetry.savedMemory p.toRetry).size := target.2.2.2.trans sourceSize.symm
  have hm : (registerSaved p).max=(AllocateRetry.savedMemory p.toRetry).max := target.2.2.1.trans source.2.2.symm
  have result := AllocateSetupGrowth.grow_eq_of_shape _ (registerSaved p) p.grown (registerDelta p).toNat hs hm hg
  simpa only [registerGrown,AllocateSetupGrowth.grownMemory] using result

theorem register_growth_native (p : Layout) (hn : Native p) :
    AllocateGrowth.Native (AllocateRetry.growthLayout (actualRegister p).toRetry) := by
  let q := AllocateRetry.growthLayout (actualRegister p).toRetry
  have old := hn.register.allocation.growth
  have target := registerSaved_spec p hn
  have nums := AllocateVector.stack_numbers p.toVector (hn.register.vector_original p.toRegisterOuter).vector
  have low := (hn.register.vector_original p.toRegisterOuter).vector.spLower
  have bound := (hn.register.vector_original p.toRegisterOuter).vector.spBound
  have memoryEq : q.memory=registerSaved p := by
    simp only [q,AllocateRetry.growthLayout,AllocateRetry.savedMemory,AllocatePositive.savedMemory,
      AllocatePositive.scratch,actualRegister,registerTemplate,registerSaved]
  have deltaEq : AllocateGrowth.delta q=registerDelta p := rfl
  have sizeEq : q.memory.size=p.memory.size := by rw [memoryEq];exact target.2.2.2
  have wf : q.memory.wf := by rw [memoryEq];exact target.1
  have grownEq : q.grown=registerGrown p := rfl
  have grow : q.memory.grow (AllocateGrowth.delta q).toNat=some q.grown := by
    rw [memoryEq,deltaEq,grownEq]
    exact register_grow p hn
  have recordBound : q.record.toNat+8≤q.memory.byteSize := by
    rw [memoryEq,target.2.1]
    change (p.sp-16).toNat+8≤p.memory.byteSize
    rw [nums.2.2.2.2.1];omega
  refine ⟨old.wordsBound,old.alignAdd,old.alignMask,old.padAdd,old.roundBound,
    old.pagesBound,old.pagesPositive,?_,wf,grow,recordBound⟩
  rw [sizeEq]
  have source := AllocateRetry.saved_size p.toRetry hn.register.allocation
  have h := old.oldPagesBound
  change (AllocateRetry.savedMemory p.toRetry).size<65536 at h
  rw [source] at h
  exact h


theorem register_native (p : Layout) (hn : Native p) (haRoot : p.allocator=1074896) :
    StateReadRegisterOuter.Native (actualRegister p) := by
  have old := hn.register
  have shape := storageMemory_footprint p hn
  have low := hn.spLower
  have bound := hn.spBound
  have heap : p.sp548.toNat≤p.allocator.toNat := by
    have a := hn.vtableAbove
    have b := hn.vtableBeforeHeap
    omega
  have empty := (storageMemory_word p hn p.allocator.toNat heap
    (by left;rw [haRoot];decide)).trans old.allocation.empty
  have allocatorBound : p.allocator.toNat+4≤(storageMemory p).byteSize := by rw [shape.2.1];exact old.allocation.allocatorBound
  have width : (storageMemory p).byteSize≤2^32 := by rw [shape.2.1];exact old.allocation.width
  have spBound : p.sp.toNat≤(storageMemory p).byteSize := by rw [shape.2.1];exact old.allocation.spBound
  have oldPositive : 0<(storageMemory p).size := by rw [storageMemory_size p hn];exact old.allocation.oldPositive
  have pages : (storageMemory p).size+(registerDelta p).toNat<65536 := by rw [storageMemory_size p hn];exact old.allocation.pagesBound
  have vt : 1057464+20≤(storageMemory p).byteSize := by rw [shape.2.1];exact old.allocation.vtableBound
  have child : AllocateZeroedRetry.Native (actualRegister p).toZeroed :=
    ⟨old.allocation.positive,old.allocation.rounding,shape.1,width,old.allocation.spLower,spBound,
      allocatorBound,empty,register_growth_native p hn,oldPositive,pages,old.allocation.wordsPositive,
      old.allocation.room,vt,old.allocation.callbackSep⟩
  have iface : readI32 (storageMemory p) 1055020=p.lookupElement := by
    rw [storageMemory_word p hn 1055020 hn.staticAbove (Or.inl (by decide))]
    exact old.interfaceRead
  have status : readI32 (storageMemory p) 1074900=1 := by
    rw [storageMemory_word p hn 1074900 hn.threadAbove (Or.inl (by decide))]
    exact old.threadStatus
  have receiver : readI32 (storageMemory p) 1074908≠0 := by
    rw [storageMemory_word p hn 1074908 (by have := hn.threadAbove;omega) (Or.inr (by decide))]
    exact old.receiverNonzero
  have vtable : readI32 (storageMemory p) 1074912=p.dispatchVtable := by
    rw [storageMemory_word p hn 1074912 (by have := hn.threadAbove;omega) (Or.inr (by decide))]
    exact old.vtableRead
  have zero : readI32 (storageMemory p) 1074904=0 := by unfold storageMemory;exact storage_counter_restored p hn
  refine ⟨child,old.vectorFlag,old.vectorSP,old.outerSP,old.childSP,old.childOut,old.vectorOut,old.innerOut,
    old.vectorGlobal,old.outerGlobal,old.childGlobal,old.spLower,?_,old.aligned,old.positive,old.sizeBound,old.size,
    ?_,old.heapAbove,old.callbackAbove,old.staticAbove,?_,iface,?_,status,zero,receiver,vtable,
    old.vtableAbove,old.vtableBeforeHeap,?_⟩
  · change p.sp523.toNat≤(storageMemory p).byteSize;rw [shape.2.1];exact old.spBound
  · change p.out523.toNat+12≤(storageMemory p).byteSize;rw [shape.2.1];exact old.outputBound
  · change 1055024≤(storageMemory p).byteSize;rw [shape.2.1];exact old.interfaceBound
  · change 1074916≤(storageMemory p).byteSize;rw [shape.2.1];exact old.threadBound
  · change p.dispatchVtable.toNat+20≤(storageMemory p).byteSize;rw [shape.2.1];exact old.vtableBound
end WNear.Proofs.StateReadStorageOuter
