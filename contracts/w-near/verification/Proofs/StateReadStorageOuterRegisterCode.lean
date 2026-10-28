import Proofs.StateReadStorageOuterRegisterNative
import Proofs.StateReadStorageOuterCode
import Proofs.StateReadRegisterOuterReadCode
import Proofs.StateReadRegisterOuterVectorCode

/-! All523 installed code is transported across actual459, including its allocator
callback and both original-memory SDK selectors. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 storageMemory registerSaved registerDelta AllocateSetupGrowth.grownMemory

theorem Code.registerCode (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (h : Code s inst p extra) :
    StateReadRegisterOuter.Code s inst (actualRegister p) extra := by
  have native := register_native p hn ha
  have old := h.register
  have original := hn.register
  have cbAbove : p.sp548.toNat≤1057464+16 := by have := hn.staticAbove;omega
  have currentAbove : (actualRegister p).sp523.toNat≤1057464+16 := by
    have nums := stack_numbers p hn
    have lower := hn.spLower
    change p.sp523.toNat≤_
    rw [hn.registerSP,nums.1];omega
  have source := StateReadRegisterOuter.originalSaved_word p.toRegisterOuter original _ original.callbackAbove
  have target := StateReadRegisterOuter.originalSaved_word (actualRegister p) native _ currentAbove
  have memoryEq : (actualRegister p).memory=storageMemory p := by simp only [actualRegister,registerTemplate]
  have selector : readI32 (AllocatePositive.searchLayout (actualRegister p).toLayout).memory (1057464+16)=
      readI32 (AllocatePositive.searchLayout p.toLayout).memory (1057464+16) := by
    have cb := storageMemory_word p hn _ cbAbove (Or.inl (by decide))
    rw [memoryEq] at target
    have all := target.trans (cb.trans source.symm)
    simpa only [AllocatePositive.searchLayout,AllocatePositive.savedMemory,AllocatePositive.scratch,AllocateRetry.savedMemory] using all
  have positiveOld := old.vector.vector.allocation.allocation.retry.originalCode
  have search : AllocateSearch.SearchCode s (AllocatePositive.searchLayout (actualRegister p).toLayout) inst := by
    refine {positiveOld.search with callbackElement:=?_}
    change p.table.elems[(readI32 (AllocatePositive.searchLayout (actualRegister p).toLayout).memory (1057464+16)).toNat]?=some (.func p.callbackAddress)
    rw [selector]
    exact positiveOld.search.callbackElement
  have positive : AllocatePositive.Code s inst (actualRegister p).toLayout := {positiveOld with search:=search}
  have retry : AllocateRetry.Code s inst (actualRegister p).toRetry := {old.vector.vector.allocation.allocation.retry with originalCode:=positive}
  have zeroed : AllocateZeroedRetry.Code s inst (actualRegister p).toZeroed := {old.vector.vector.allocation.allocation with retry:=retry}
  have record : AllocateRecord.Code s inst (actualRegister p).toRecord := {old.vector.vector.allocation with allocation:=zeroed}
  have vector : AllocateVector.Code s inst (actualRegister p).toVector := {old.vector.vector with allocation:=record}
  have outer : AllocateVectorOuter.Code s inst (actualRegister p).toVectorOuter := {old.vector with vector:=vector}
  have vtAbove := hn.vtableAbove
  have before := hn.vtableBeforeHeap
  rw [ha] at before
  change p.dispatchVtable.toNat+192≤1074896 at before
  have len : readI32 (actualRegister p).memory ((actualRegister p).dispatchVtable.toNat+16)=readI32 p.memory (p.dispatchVtable.toNat+16) := by
    have vt : (actualRegister p).dispatchVtable=p.dispatchVtable := by simp only [actualRegister,registerTemplate]
    rw [memoryEq,vt]
    exact storageMemory_word p hn _ (by omega) (Or.inl (by omega))
  have readEq : StateDispatchRead.element (StateReadRegisterOuter.originalReadLayout (actualRegister p))=
      StateDispatchRead.element (StateReadRegisterOuter.originalReadLayout p.toRegisterOuter) := by
    rw [StateReadRegisterOuter.original_read_element (actualRegister p) native (by simpa only [actualRegister,registerTemplate] using ha),
      StateReadRegisterOuter.original_read_element p.toRegisterOuter original ha]
    have vt : (actualRegister p).dispatchVtable=p.dispatchVtable := by simp only [actualRegister,registerTemplate]
    rw [memoryEq,vt]
    exact storageMemory_word p hn _ (by omega) (Or.inl (by omega))
  have rp := old.readCode.prefixCode
  have readPrefix : StateDispatchPrefix.Code s (StateReadRegisterOuter.originalReadLayout (actualRegister p)).toLayout inst :=
    ⟨rp.module,rp.tableIndex,rp.table,rp.lookupElement,rp.lookupType,rp.lookupFunction,rp.helperIndex,rp.helperFunction,
      rp.acquireLinks,rp.acquireIndex,rp.acquireFunction,rp.memoryIndex,rp.globalIndex⟩
  have read : StateDispatchRead.Code s (StateReadRegisterOuter.originalReadLayout (actualRegister p)) inst extra := by
    refine {old.readCode with prefixCode:=readPrefix,readElement:=?_}
    rw [readEq];exact old.readCode.readElement
  have lp := old.prefixCode
  have prefixCode : StateDispatchPrefix.Code s (StateReadRegisterOuter.actualLength (actualRegister p)).inner.toLayout inst :=
    ⟨lp.module,lp.tableIndex,lp.table,lp.lookupElement,lp.lookupType,lp.lookupFunction,lp.helperIndex,lp.helperFunction,
      lp.acquireLinks,lp.acquireIndex,lp.acquireFunction,lp.memoryIndex,lp.globalIndex⟩
  refine {old with vector:=outer,prefixCode:=prefixCode,lengthElement:=?_,readCode:=read}
  rw [len]
  exact old.lengthElement
end WNear.Proofs.StateReadStorageOuter
