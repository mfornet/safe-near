import Proofs.StateReadRegisterOuterBorrow

/-! The actual524 native domain follows from original523 stack/static words. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 StateDispatchLength.lowMemory

theorem length_vtable_eq (p : Layout) (hn : Native p) :
    StateDispatchLength.vtable (actualLength p).inner=p.dispatchVtable := by
  unfold StateDispatchLength.vtable
  rw [selected_eq p hn]
  change readI32 (StateDispatchLength.lowMemory (actualLength p).inner) 1074912=p.dispatchVtable
  have above : p.sp523.toNat≤1074912 := by have := hn.staticAbove;omega
  exact (low_static_word p hn 1074912 above (Or.inr (by decide))).trans hn.vtableRead

theorem length_native (p : Layout) (hn : Native p) : StateDispatchLengthOuter.Native (actualLength p) := by
  have prep := prepared_spec p hn
  have shapes := borrow_shapes p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have static := hn.staticAbove
  have cell := hn.threadBound
  have bs : (StateDispatchLength.scratch (actualLength p).inner).toNat=p.sp523.toNat-80 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,actualLength,lengthOn] using nums.2.2.1
  have inputNat : (actualLength p).inner.input.toNat=p.sp523.toNat-56 := by
    change (scratch p-16+8).toNat=p.sp523.toNat-56
    rw [UInt32.toNat_add,nums.2.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have upper := p.sp523.toNat_lt
    omega
  have counterZero : readI32 (actualLength p).inner.memory 1074904=0 :=
    (prepared_word p hn 1074904 (by omega)).trans hn.counterZero
  have count : Numeric.irelop32 .ge_s (ValueReturnAcquire.nextCount (actualLength p).inner.memory 1074904) 1=true := by
    simp only [ValueReturnAcquire.nextCount,show (1074904:UInt32).toNat=1074904 by decide,counterZero]
    decide
  have interfaceRead : readI32 (actualLength p).inner.memory 1055020=p.lookupElement :=
    (prepared_word p hn 1055020 hn.staticAbove).trans hn.interfaceRead
  have threadRead : readI32 (actualLength p).inner.memory 1074900=1 :=
    (prepared_word p hn 1074900 (by omega)).trans hn.threadStatus
  have highBound : (StateDispatchLength.scratch (actualLength p).inner).toNat+16≤
      (StateDispatchLength.acquiredMemory (actualLength p).inner).byteSize := by
    rw [shapes.2.1,bs];omega
  have lowBound : (StateDispatchLength.scratch (actualLength p).inner).toNat+12≤
      (StateDispatchLength.highMemory (actualLength p).inner).byteSize := by
    rw [shapes.2.2.2.1,bs];omega
  have selectBound : (StateDispatchLength.borrowed (actualLength p).inner).toNat+4≤
      (StateDispatchLength.lowMemory (actualLength p).inner).byteSize := by
    rw [borrowed_eq p hn,shapes.2.2.2.2.2]
    change 1074908+4≤p.memory.byteSize
    omega
  have selectedNonzero : StateDispatchLength.selected (actualLength p).inner≠0 := by
    rw [selected_eq p hn];decide
  have selectedBound : (StateDispatchLength.selected (actualLength p).inner).toNat+8≤
      (StateDispatchLength.lowMemory (actualLength p).inner).byteSize := by
    rw [selected_eq p hn,shapes.2.2.2.2.2]
    change 1074908+8≤p.memory.byteSize
    omega
  have inputBound : (actualLength p).inner.input.toNat+8≤
      (StateDispatchLength.lowMemory (actualLength p).inner).byteSize := by
    rw [inputNat,shapes.2.2.2.2.2];omega
  have vtableBound : (StateDispatchLength.vtable (actualLength p).inner).toNat+20≤
      (StateDispatchLength.lowMemory (actualLength p).inner).byteSize := by
    rw [length_vtable_eq p hn,shapes.2.2.2.2.2];exact hn.vtableBound
  have releaseBound : ((StateDispatchLength.scratch (actualLength p).inner+8)|||4).toNat+4≤
      (StateDispatchLength.lowMemory (actualLength p).inner).byteSize := by
    rw [release_address p hn,bs,shapes.2.2.2.2.2];omega
  have counterBound : (StateDispatchLength.counter (actualLength p).inner).toNat+4≤
      (StateDispatchLength.lowMemory (actualLength p).inner).byteSize := by
    rw [counter_eq p hn,shapes.2.2.2.2.2]
    change 1074904+4≤p.memory.byteSize
    omega
  refine ⟨?_,rfl,rfl,rfl,rfl,?_,interfaceRead,?_,threadRead,?_,?_,count,
    highBound,lowBound,selectBound,selectedNonzero,selectedBound,inputBound,vtableBound,releaseBound,counterBound⟩
  · rfl
  · change 1055020+4≤(actualLength p).inner.memory.byteSize
    rw [prep.2.1];exact hn.interfaceBound
  · rw [prep.2.1];omega
  · rw [prep.2.1];omega
  · rw [bs,prep.2.1];omega
end WNear.Proofs.StateReadRegisterOuter
