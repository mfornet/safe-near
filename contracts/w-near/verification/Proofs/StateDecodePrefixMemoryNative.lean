import Proofs.StateDecodePrefixPhases
import Proofs.StateDecodeVectorCopyMemory

/-! Original accepted316 geometry gives all memory resources needed after374
and for the final stores. No post-allocation memory predicate is assumed. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] allocatedMemory droppedMemory readI32 StateDecodeVectorCopy.finalMemory takenPayloadMemory StateDecodeSlices.finalMemory

theorem allocatedMemory_spec (p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    (allocatedMemory p q).wf ∧(allocatedMemory p q).byteSize=p.memory.byteSize ∧(allocatedMemory p q).max=p.memory.max:=by
  have n:=allocation_copy_native p q hn hd
  have h:=StateDecodeVectorCopy.finalMemory_spec (allocationInput p q) n
  have t:=takenPayload_spec p hn
  unfold allocatedMemory
  exact ⟨h.1,h.2.1.trans t.2.1,h.2.2.1.trans t.2.2.1⟩

theorem droppedMemory_spec (p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    (droppedMemory p q).wf ∧(droppedMemory p q).byteSize=p.memory.byteSize ∧(droppedMemory p q).max=p.memory.max:=by
  have a:=allocatedMemory_spec p q hn hd
  have add:(dropPayloadOut p).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have endsp:=scratch_end p hn
  have spb:=hn.spBound
  have b:(dropPayloadOut p).toNat+8≤(allocatedMemory p q).byteSize:=by rw[add,a.2.1];omega
  have h:=StateDecodeSlices.finalMemory_spec true (allocatedMemory p q) (dropPayloadOut p)
    (readI32 (allocatedMemory p q) p.slice.toNat) (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p) a.1 b
  unfold droppedMemory
  exact ⟨h.1,h.2.1.trans a.2.1,h.2.2.1.trans a.2.2⟩

theorem output_native (p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):Output.Native (outputLayout p q):=by
  have h:=droppedMemory_spec p q hn hd
  have e:=scratch_end p hn
  have b:=hn.spBound
  refine ⟨h.1,?_,?_,?_,?_⟩
  · change (droppedMemory p q).byteSize≤2^32
    rw[h.2.1];exact hn.memoryWidth
  · change p.out.toNat+16≤(droppedMemory p q).byteSize
    rw[h.2.1];exact hn.outBound
  · change (scratch p).toNat+64≤(droppedMemory p q).byteSize
    rw[h.2.1];omega
  · change p.slice.toNat+8≤(droppedMemory p q).byteSize
    rw[h.2.1];exact hn.sliceBound
end WNear.Proofs.StateDecodePrefix
