import Proofs.AllocateVectorState
import Proofs.AllocateLayoutWrapperFootprint
import Proofs.AllocateSetupGrowthCanonical
import Proofs.AllocateRetryDomain

/-! Reconstruct the690 allocator domain from original686 memory and native bounds. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 laidOutMemory targetSaved

theorem stack_numbers (p : Layout) (hn : Native p) :
    (reservedSP p).toNat=p.outerSP.toNat-32 ∧
    p.sp.toNat=p.outerSP.toNat-48 ∧
    (AllocateLayoutWrapper.scratch (layout685 p)).toNat=p.sp.toNat ∧
    (layout685 p).out.toNat=p.outerSP.toNat-8 ∧
    (p.sp-16).toNat=p.outerSP.toNat-64 ∧
    p.out.toNat=p.outerSP.toNat-40 ∧
    (reservedSP p+8).toNat=p.outerSP.toNat-24 := by
  have lower := hn.spLower
  have upper := p.outerSP.toNat_lt
  have r : (reservedSP p).toNat=p.outerSP.toNat-32 := by
    rw [reservedSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have t : p.sp.toNat=p.outerSP.toNat-48 := by
    rw [hn.childSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have scratch : (AllocateLayoutWrapper.scratch (layout685 p)).toNat=p.sp.toNat := by
    change (reservedSP p-16).toNat=p.sp.toNat
    rw [UInt32.toNat_sub,r]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have out : (layout685 p).out.toNat=p.outerSP.toNat-8 := by
    change (reservedSP p+24).toNat=p.outerSP.toNat-8
    rw [UInt32.toNat_add,r]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have save : (p.sp-16).toNat=p.outerSP.toNat-64 := by
    rw [UInt32.toNat_sub,t]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have child : p.out.toNat=p.outerSP.toNat-40 := by
    rw [hn.childOut,UInt32.toNat_add,t]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have copy : (reservedSP p+8).toNat=p.outerSP.toNat-24 := by
    rw [UInt32.toNat_add,r]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨r,t,scratch,out,save,child,copy⟩

theorem setup_bounds (p : Layout) (hn : Native p) :
    (AllocateLayoutWrapper.scratch (layout685 p)).toNat+16≤p.memory.byteSize ∧
    (layout685 p).out.toNat+8≤p.memory.byteSize := by
  have nums := stack_numbers p hn
  have bound := hn.spBound
  have lower := hn.spLower
  simp only [nums.2.2.1,nums.2.2.2.1,nums.2.1]
  omega

theorem setup_spec (p : Layout) (hn : Native p) :
    (laidOutMemory p).wf ∧ (laidOutMemory p).byteSize=p.memory.byteSize ∧
    (laidOutMemory p).max=p.memory.max ∧ (laidOutMemory p).size=p.memory.size := by
  have bounds := setup_bounds p hn
  have shape := AllocateLayoutWrapper.final_footprint (layout685 p) hn.allocation.wf bounds.1 bounds.2
  unfold laidOutMemory
  exact ⟨shape.1,shape.2.1,shape.2.2.1,
    AllocateLayoutWrapper.final_size (layout685 p) hn.allocation.wf bounds.1 bounds.2⟩

theorem setup_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.outerSP.toNat≤address) :
    readI32 (laidOutMemory p) address=readI32 p.memory address := by
  have bounds := setup_bounds p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  unfold laidOutMemory
  apply AllocateLayoutWrapper.final_word_frame (layout685 p) hn.allocation.wf bounds.1 bounds.2 address
  · right;rw [nums.2.2.1,nums.2.1];omega
  · right;rw [nums.2.2.2.1];omega

theorem targetSaved_spec (p : Layout) (hn : Native p) :
    (targetSaved p).wf ∧ (targetSaved p).byteSize=p.memory.byteSize ∧
    (targetSaved p).max=p.memory.max ∧ (targetSaved p).size=p.memory.size := by
  have shape := setup_spec p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have hb : (p.sp-16).toNat+12+4≤(laidOutMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.1];omega
  have saved := writeI32_spec (laidOutMemory p) ((p.sp-16).toNat+12)
    (readI32 (laidOutMemory p) p.allocator.toNat) shape.1 hb
  have wf : (targetSaved p).wf := by simpa only [targetSaved] using saved.1
  have bytes : (targetSaved p).byteSize=p.memory.byteSize := by
    simpa only [targetSaved] using saved.2.1.trans shape.2.1
  have maxEq : (targetSaved p).max=p.memory.max := by
    simpa only [targetSaved] using saved.2.2.1.trans shape.2.2.1
  have sizeEq : (targetSaved p).size=p.memory.size := by
    change (targetSaved p).size*65536=p.memory.size*65536 at bytes
    omega
  exact ⟨wf,bytes,maxEq,sizeEq⟩

theorem target_grow (p : Layout) (hn : Native p) :
    (targetSaved p).grow (delta p).toNat=some (derivedGrown p) := by
  have source := AllocateRetry.saved_shape p.toRecord.toZeroed.toRetry hn.allocation
  have sourceSize := AllocateRetry.saved_size p.toRecord.toZeroed.toRetry hn.allocation
  have target := targetSaved_spec p hn
  have hg := hn.allocation.growth.grow
  have hs : (targetSaved p).size=(AllocateRetry.savedMemory p.toRecord.toZeroed.toRetry).size :=
    target.2.2.2.trans sourceSize.symm
  have hm : (targetSaved p).max=(AllocateRetry.savedMemory p.toRecord.toZeroed.toRetry).max :=
    target.2.2.1.trans source.2.2.symm
  have result := AllocateSetupGrowth.grow_eq_of_shape _ (targetSaved p) p.grown (delta p).toNat hs hm hg
  simpa only [derivedGrown,AllocateSetupGrowth.grownMemory] using result

theorem growth_native (p : Layout) (hn : Native p) :
    AllocateGrowth.Native (AllocateRetry.growthLayout (actualRecord p).toZeroed.toRetry) := by
  let q := AllocateRetry.growthLayout (actualRecord p).toZeroed.toRetry
  have old := hn.allocation.growth
  have target := targetSaved_spec p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have memoryEq : q.memory=targetSaved p := by
    simp only [q,AllocateRetry.growthLayout,AllocateRetry.savedMemory,AllocatePositive.savedMemory,
      AllocatePositive.scratch,actualRecord,targetSaved]
  have wordsEq : q.words=(AllocateRetry.growthLayout p.toRecord.toZeroed.toRetry).words := rfl
  have deltaEq : AllocateGrowth.delta q=delta p := rfl
  have sizeEq : q.memory.size=p.memory.size := by rw [memoryEq];exact target.2.2.2
  have wf : q.memory.wf := by rw [memoryEq];exact target.1
  have grow : q.memory.grow (AllocateGrowth.delta q).toNat=some q.grown := by
    rw [memoryEq,deltaEq]
    exact target_grow p hn
  have recordBound : q.record.toNat+8≤q.memory.byteSize := by
    rw [memoryEq,target.2.1]
    change (p.sp-16).toNat+8≤p.memory.byteSize
    rw [nums.2.2.2.2.1];omega
  refine ⟨old.wordsBound,old.alignAdd,old.alignMask,old.padAdd,old.roundBound,
    old.pagesBound,old.pagesPositive,?_,wf,grow,recordBound⟩
  rw [sizeEq]
  have source := AllocateRetry.saved_size p.toRecord.toZeroed.toRetry hn.allocation
  have h := old.oldPagesBound
  change (AllocateRetry.savedMemory p.toRecord.toZeroed.toRetry).size<65536 at h
  rw [source] at h
  exact h

theorem allocation_native (p : Layout) (hn : Native p) :
    AllocateRecord.Native (actualRecord p) := by
  have shape := setup_spec p hn
  have nums := stack_numbers p hn
  have low := hn.spLower
  have bound := hn.spBound
  have width := hn.allocation.width
  have empty := (setup_word p hn p.allocator.toNat hn.heapAbove).trans hn.allocation.empty
  have spLower : 16≤p.sp.toNat := by rw [nums.2.1];omega
  have spBound : p.sp.toNat≤(laidOutMemory p).byteSize := by rw [shape.2.1,nums.2.1];omega
  have allocatorBound : p.allocator.toNat+4≤(laidOutMemory p).byteSize := by
    rw [shape.2.1];exact hn.allocation.allocatorBound
  have widthAfter : (laidOutMemory p).byteSize≤2^32 := by rw [shape.2.1];exact width
  have oldPositive : 0<(laidOutMemory p).size := by rw [shape.2.2.2];exact hn.allocation.oldPositive
  have pagesBound : (laidOutMemory p).size+(delta p).toNat<65536 := by
    rw [shape.2.2.2];exact hn.allocation.pagesBound
  have vtableBound : 1057464+20≤(laidOutMemory p).byteSize := by
    rw [shape.2.1];exact hn.allocation.vtableBound
  have callbackSep : (p.sp-16).toNat+16≤1057464+16 ∨ 1057464+20≤(p.sp-16).toNat := by
    left
    rw [nums.2.2.2.2.1]
    have sep := hn.callbackAbove
    omega
  have child : AllocateZeroedRetry.Native (actualRecord p).toZeroed :=
    ⟨hn.allocation.positive,hn.allocation.rounding,shape.1,widthAfter,spLower,spBound,
      allocatorBound,empty,growth_native p hn,oldPositive,pagesBound,hn.allocation.wordsPositive,
      hn.allocation.room,vtableBound,callbackSep⟩
  have outputBound : p.out.toNat+8≤(laidOutMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.2.1];omega
  exact ⟨child,outputBound⟩

theorem copy_native (p : Layout) (hn : Native p) : AllocateRecordCopy.Native (layout690 p) := by
  have nums := stack_numbers p hn
  have shape := setup_spec p hn
  have low := hn.spLower
  have bound := hn.spBound
  have upper := p.outerSP.toNat_lt
  have childSP : p.sp=reservedSP p-16 := by
    apply UInt32.toNat_inj.mp
    rw [nums.2.1,UInt32.toNat_sub,nums.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have outputBound : (reservedSP p+8).toNat+8≤(laidOutMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.2.2];omega
  have scratchBound : p.sp.toNat+16≤(laidOutMemory p).byteSize := by
    rw [shape.2.1,nums.2.1];omega
  refine ⟨allocation_native p hn,childSP,hn.childOut,?_,outputBound,scratchBound⟩
  simp only [layout690,actualRecord]
  exact hn.childGlobal
end WNear.Proofs.AllocateVector
