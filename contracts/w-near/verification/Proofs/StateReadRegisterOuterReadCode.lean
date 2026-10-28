import Proofs.StateReadRegisterOuterReadDomain
import Proofs.StateReadRegisterOuterCode

/-! Installed read-register dispatch code transfers from original selector words
through actual524/687 memory effects. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StateReadRegisterOuterReadMemory
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 readInputMemory

theorem original_read_element (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    StateDispatchRead.element (originalReadLayout p)=readI32 p.memory (p.dispatchVtable.toNat+12) := by
  let q := originalReadLayout p
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have above := hn.staticAbove
  have vAbove := hn.vtableAbove
  have cell := hn.threadBound
  have vBefore := hn.vtableBeforeHeap
  rw [ha] at vBefore
  change p.dispatchVtable.toNat+20≤1074896 at vBefore
  have scratchNat : (StateDispatchRead.scratch q).toNat=p.sp523.toNat-64 := nums.2.1
  have scratchBound : (StateDispatchRead.scratch q).toNat+16≤p.memory.byteSize := by
    rw [scratchNat];have := hn.spBound;omega
  have selected : StateDispatchRead.selected q=1074908 :=
    StateReadRegisterOuterReadMemory.selected_eq q hn.allocation.wf (by change 1074908≤p.memory.byteSize;omega) scratchBound
      (Or.inr (by rw [scratchNat];omega)) hn.receiverNonzero
  have vt : StateDispatchRead.vtable q=p.dispatchVtable := by
    unfold StateDispatchRead.vtable
    rw [selected]
    change readI32 (StateDispatchRead.lowMemory q) 1074912=_
    rw [low_read_frame q 1074912 hn.allocation.wf (by change 1074908≤p.memory.byteSize;omega) scratchBound
      (Or.inr (by omega)) (Or.inr (by rw [scratchNat];omega))]
    exact hn.vtableRead
  unfold StateDispatchRead.element
  rw [vt]
  exact low_read_frame q (p.dispatchVtable.toNat+12) hn.allocation.wf
    (by change 1074908≤p.memory.byteSize;omega) scratchBound (Or.inl (by omega))
    (Or.inr (by rw [scratchNat];omega))

theorem read_element_eq (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    StateDispatchRead.element (readLayout p)=StateDispatchRead.element (originalReadLayout p) := by
  rw [(read_snapshot p hn ha).element,original_read_element p hn ha]
  have vb := hn.vtableBound
  have va := hn.vtableAbove
  have before := hn.vtableBeforeHeap
  rw [ha] at before
  change p.dispatchVtable.toNat+20≤1074896 at before
  exact read_original_word p hn ha (p.dispatchVtable.toNat+12) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))

theorem Code.actualRead (s : Store NearState) (inst : Nat) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (h : Code s inst p extra) :
    StateDispatchRead.Code s (readLayout p) inst extra := by
  have old := h.readCode
  have pre := old.prefixCode
  have prefixCode : StateDispatchPrefix.Code s (readLayout p).toLayout inst :=
    ⟨pre.module,pre.tableIndex,pre.table,pre.lookupElement,pre.lookupType,pre.lookupFunction,
     pre.helperIndex,pre.helperFunction,pre.acquireLinks,pre.acquireIndex,pre.acquireFunction,pre.memoryIndex,pre.globalIndex⟩
  refine ⟨prefixCode,old.nonnullIndex,old.nonnullFunction,old.releaseIndex,old.releaseFunction,
    old.swapIndex,old.swapFunction,old.returnIndex,old.returnFunction,?_,old.readType,old.readIndex,old.readFunction,old.hostIndex,old.hostFunction⟩
  rw [read_element_eq p hn ha]
  exact old.readElement
end WNear.Proofs.StateReadRegisterOuter
