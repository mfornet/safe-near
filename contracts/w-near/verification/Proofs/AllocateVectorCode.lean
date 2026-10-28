import Binary.AllocateVector
import Proofs.AllocateVectorNative

/-! Actual installed code and the callback selector after the concrete685 stack writes. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 laidOutMemory targetSaved

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  allocation : AllocateRecord.Code s inst p.toRecord
  index684 : p.mi.funcAddrs[684]?=some p.address684
  function684 : s.funcs[p.address684]?=some (.wasm WNear.Binary.AllocateLayout.signature inst WNear.Binary.AllocateLayout.function684)
  index685 : p.mi.funcAddrs[685]?=some p.address685
  function685 : s.funcs[p.address685]?=some (.wasm WNear.Binary.AllocateLayout.signature inst WNear.Binary.AllocateLayout.function685)
  index689 : p.mi.funcAddrs[689]?=some p.address689
  function689 : s.funcs[p.address689]?=some (.wasm WNear.Binary.AllocateRecord.signature inst WNear.Binary.AllocateRecord.function)
  index690 : p.mi.funcAddrs[690]?=some p.address690
  function690 : s.funcs[p.address690]?=some (.wasm WNear.Binary.AllocateRecordCopy.signature inst WNear.Binary.AllocateRecordCopy.function)

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  refine ⟨h.allocation.transport s t inst p.toRecord hf hm ht,h.index684,?_,h.index685,?_,h.index689,?_,h.index690,?_⟩
  · rw [hf];exact h.function684
  · rw [hf];exact h.function685
  · rw [hf];exact h.function689
  · rw [hf];exact h.function690

theorem targetSaved_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.outerSP.toNat≤address) :
    readI32 (targetSaved p) address=readI32 p.memory address := by
  have shape := setup_spec p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have hb : (p.sp-16).toNat+12+4≤(laidOutMemory p).byteSize := by
    rw [shape.2.1,nums.2.2.2.2.1];omega
  have sep : (p.sp-16).toNat+12+4≤address := by rw [nums.2.2.2.2.1];omega
  have frame := PanicAllocateReadback.read_write_frame (laidOutMemory p) address ((p.sp-16).toNat+12)
    (readI32 (laidOutMemory p) p.allocator.toNat) shape.1 hb (Or.inr sep)
  unfold targetSaved
  exact frame.trans (setup_word p hn address ha)

theorem saved_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.outerSP.toNat≤address) :
    readI32 (AllocateRetry.savedMemory p.toRecord.toZeroed.toRetry) address=readI32 p.memory address := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have hb : (p.sp-16).toNat+12+4≤p.memory.byteSize := by rw [nums.2.2.2.2.1];omega
  have sep : (p.sp-16).toNat+12+4≤address := by rw [nums.2.2.2.2.1];omega
  exact PanicAllocateReadback.read_write_frame p.memory address ((p.sp-16).toNat+12)
    (readI32 p.memory p.allocator.toNat) hn.allocation.wf hb (Or.inr sep)

theorem callback_word (p : Layout) (hn : Native p) :
    readI32 (targetSaved p) (1057464+16)=
    readI32 (AllocateRetry.savedMemory p.toRecord.toZeroed.toRetry) (1057464+16) :=
  (targetSaved_word p hn _ hn.callbackAbove).trans (saved_word p hn _ hn.callbackAbove).symm

theorem Code.record (s : Store NearState) (inst : Nat) (p : Layout)
    (hn : Native p) (h : Code s inst p) : AllocateRecord.Code s inst (actualRecord p) := by
  have old := h.allocation.allocation.retry.originalCode
  have callback := callback_word p hn
  have selector : readI32 (AllocatePositive.searchLayout (actualRecord p).toZeroed.toRetry.toLayout).memory (1057464+16)=
      readI32 (AllocatePositive.searchLayout p.toRecord.toZeroed.toRetry.toLayout).memory (1057464+16) := by
    simpa only [AllocatePositive.searchLayout,AllocatePositive.savedMemory,AllocatePositive.scratch,
      AllocateRetry.savedMemory,actualRecord,targetSaved] using callback
  have search : AllocateSearch.SearchCode s
      (AllocatePositive.searchLayout (actualRecord p).toZeroed.toRetry.toLayout) inst := by
    refine {old.search with callbackElement:=?_}
    change p.table.elems[(readI32 (AllocatePositive.searchLayout (actualRecord p).toZeroed.toRetry.toLayout).memory (1057464+16)).toNat]?=some (.func p.callbackAddress)
    rw [selector]
    exact old.search.callbackElement
  have positive : AllocatePositive.Code s inst (actualRecord p).toZeroed.toRetry.toLayout :=
    {old with search:=search}
  have retry : AllocateRetry.Code s inst (actualRecord p).toZeroed.toRetry :=
    {h.allocation.allocation.retry with originalCode:=positive}
  have zeroed : AllocateZeroedRetry.Code s inst (actualRecord p).toZeroed :=
    {h.allocation.allocation with retry:=retry}
  exact {h.allocation with allocation:=zeroed}

theorem Code.copy (s : Store NearState) (inst : Nat) (p : Layout)
    (hn : Native p) (h : Code s inst p) : AllocateRecordCopy.Code s inst (layout690 p) :=
  ⟨h.record s inst p hn,h.index689,h.function689⟩
end WNear.Proofs.AllocateVector
