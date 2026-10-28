import Proofs.StateReadRegisterOuterCode
import Proofs.StateReadRegisterOuterVectorNative

/-! The actual524 footprint preserves the original allocator callback selector,
so all installed687 code is derived on its actual post-query memory. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 lengthMemory vectorSaved

theorem vectorSaved_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.sp523.toNat≤address) (hc : address+4≤1074904 ∨ 1074908≤address) :
    readI32 (vectorSaved p) address=readI32 p.memory address := by
  have shape := lengthMemory_footprint p hn
  have original := hn.vector_original p
  have nums := AllocateVector.stack_numbers p.toVector original.vector
  have lower := original.vector.spLower
  have bound := original.vector.spBound
  have hb : (p.sp-16).toNat+12+4≤(lengthMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.1];omega
  have sep : (p.sp-16).toNat+12+4≤address := by
    rw [nums.2.2.2.2.1]
    have outer : p.outerSP.toNat≤p.sp523.toNat := by
      rw [hn.outerSP,UInt32.toNat_sub]
      simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
      have low := hn.spLower
      have upper := p.sp523.toNat_lt
      omega
    omega
  have frame := PanicAllocateReadback.read_write_frame (lengthMemory p) address ((p.sp-16).toNat+12)
    (readI32 (lengthMemory p) p.allocator.toNat) shape.1 hb (Or.inr sep)
  have eq : vectorSaved p=writeI32 (lengthMemory p) ((p.sp-16).toNat+12)
      (readI32 (lengthMemory p) p.allocator.toNat) := by unfold vectorSaved;rfl
  rw [eq]
  exact frame.trans (lengthMemory_word p hn address ha hc)

theorem originalSaved_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.sp523.toNat≤address) :
    readI32 (AllocateRetry.savedMemory p.toRetry) address=readI32 p.memory address := by
  have nums := AllocateRetry.scratch_numbers p.toRetry hn.allocation
  have child : p.sp.toNat≤p.sp523.toNat := by
    rw [hn.childSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have low := hn.spLower
    have upper := p.sp523.toNat_lt
    omega
  have spLower := hn.allocation.spLower
  have sep : (AllocateRetry.scratch p.toRetry).toNat+12+4≤address := by rw [nums.1];omega
  have frame := PanicAllocateReadback.read_write_frame p.memory address
    ((AllocateRetry.scratch p.toRetry).toNat+12) (readI32 p.memory p.allocator.toNat)
    hn.allocation.wf (by have := nums.2.2.1;omega) (Or.inr sep)
  exact frame

theorem Code.vectorCode (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (hn : Native p) (h : Code s inst p extra) : AllocateVectorOuter.Code s inst (actualVector p) := by
  have old := h.vector.vector.allocation.allocation.retry.originalCode
  have cb : readI32 (vectorSaved p) (1057464+16)=
      readI32 (AllocateRetry.savedMemory p.toRetry) (1057464+16) :=
    (vectorSaved_word p hn _ hn.callbackAbove (Or.inl (by decide))).trans
      (originalSaved_word p hn _ hn.callbackAbove).symm
  have selector : readI32 (AllocatePositive.searchLayout (actualVector p).toRecord.toZeroed.toRetry.toLayout).memory (1057464+16)=
      readI32 (AllocatePositive.searchLayout p.toLayout).memory (1057464+16) := by
    simpa only [AllocatePositive.searchLayout,AllocatePositive.savedMemory,AllocatePositive.scratch,
      AllocateRetry.savedMemory,actualVector,vectorMemoryTemplate,vectorSaved] using cb
  have search : AllocateSearch.SearchCode s
      (AllocatePositive.searchLayout (actualVector p).toRecord.toZeroed.toRetry.toLayout) inst := by
    refine {old.search with callbackElement:=?_}
    change p.table.elems[(readI32 (AllocatePositive.searchLayout (actualVector p).toRecord.toZeroed.toRetry.toLayout).memory (1057464+16)).toNat]?=some (.func p.callbackAddress)
    rw [selector]
    exact old.search.callbackElement
  have positive : AllocatePositive.Code s inst (actualVector p).toRecord.toZeroed.toRetry.toLayout := {old with search:=search}
  have retry : AllocateRetry.Code s inst (actualVector p).toRecord.toZeroed.toRetry :=
    {h.vector.vector.allocation.allocation.retry with originalCode:=positive}
  have zeroed : AllocateZeroedRetry.Code s inst (actualVector p).toRecord.toZeroed :=
    {h.vector.vector.allocation.allocation with retry:=retry}
  have record : AllocateRecord.Code s inst (actualVector p).toRecord := {h.vector.vector.allocation with allocation:=zeroed}
  have vector : AllocateVector.Code s inst (actualVector p).toVector := {h.vector.vector with allocation:=record}
  exact {h.vector with vector:=vector}
end WNear.Proofs.StateReadRegisterOuter
