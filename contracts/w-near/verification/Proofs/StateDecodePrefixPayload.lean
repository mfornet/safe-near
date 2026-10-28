import Proofs.StateDecodePrefixFinalMemorySpec
import Proofs.StateDecodePrefixAllocationCode
import Proofs.StateDecodeVectorCopySource
import Proofs.StateDecodeRawIntervalFrame

/-! Additive semantic payload preservation. The operational316 domain permits
aliases; these original source/heap/output separations are required only to
identify its final allocated bytes with the original source snapshot. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hout : j<p.out.toNat ∨p.out.toNat+16≤j)
    (hslice : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have specs:=memory_specs p hn
  have highBound:(p.out+12).toNat+4≤p.memory.byteSize:=by rw[out_address p hn];exact hn.outBound
  have high:=writeI32_spec p.memory (p.out+12).toNat (readI32 p.memory (p.scratch.toNat+56)) hn.wf highBound
  have lowBound:p.out.toNat+4+8≤(highMemory p).byteSize:=by rw[specs.2.1];have h:=hn.outBound;omega
  have low:=writeI64_spec (highMemory p) (p.out.toNat+4) (readI64 (highMemory p) (p.scratch.toNat+48)) specs.1 lowBound
  have tagBound:p.out.toNat+4≤(lowMemory p).byteSize:=by rw[specs.2.2.2.1];have h:=hn.outBound;omega
  have tag:=writeI32_spec (lowMemory p) p.out.toNat 0 specs.2.2.1 tagBound
  have descriptorBound:p.slice.toNat+8≤(tagMemory p).byteSize:=by rw[specs.2.2.2.2.2];exact hn.sliceBound
  have final:=writeI64_spec (tagMemory p) p.slice.toNat (remainder p) specs.2.2.2.2.1 descriptorBound
  have nh:¬((p.out+12).toNat≤j ∧j<(p.out+12).toNat+4):=by rw[out_address p hn];omega
  have nl:¬(p.out.toNat+4≤j ∧j<p.out.toNat+4+8):=by omega
  have nt:¬(p.out.toNat≤j ∧j<p.out.toNat+4):=by omega
  have ns:¬(p.slice.toNat≤j ∧j<p.slice.toNat+8):=by omega
  calc
    _=(tagMemory p).read8 j:=by unfold finalMemory;rw[final.2.2.2];exact ite_eq_right ns
    _=(lowMemory p).read8 j:=by unfold tagMemory;rw[tag.2.2.2];exact ite_eq_right nt
    _=(highMemory p).read8 j:=by unfold lowMemory;rw[low.2.2.2];exact ite_eq_right nl
    _=p.memory.read8 j:=by unfold highMemory;rw[high.2.2.2];exact ite_eq_right nh
end WNear.Proofs.StateDecodePrefix.Output

namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 writeI64 readI64 takenPayloadMemory allocatedMemory droppedMemory

theorem allocation_finish_eq (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q) :
    StateDecodeRaw.originalFinish (allocationInput p q).toRaw=StateDecodeRaw.originalFinish q.toRaw := by
  have next:=allocation_copy_native p q hn hd
  have old:=hd.original.vector.raw
  have root:=takenPayload_word_frame p hn q.allocator.toNat hd.heapAbove hd.descriptorRootSep
  rw[←hd.memory] at root
  have head:=takenPayload_word_frame p hn (AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat
    hd.headAbove (Or.inr hd.descriptorBeforeHead)
  rw[←hd.memory,StateDecodeRaw.original_head_eq q.toRaw old] at head
  rw[StateDecodeRaw.original_finish_eq _ next.vector.raw,StateDecodeRaw.original_finish_eq _ old]
  change Allocate.endWord (takenPayloadMemory p) (readI32 (takenPayloadMemory p) q.allocator.toNat)=Allocate.endWord q.memory (readI32 q.memory q.allocator.toNat)
  rw[root]
  unfold Allocate.endWord
  rw[head]

def payloadAddress (p : Layout) (q : StateDecodeVectorCopy.Layout) := StateDecodeVectorCopy.pointer (allocationInput p q)

theorem allocated_payload_bytes (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(payloadPointer p).toNat)
    (hroot : (payloadPointer p).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(payloadPointer p).toNat)
    (i : Nat) (hi : i<(count p).toNat) :
    (allocatedMemory p q).read8 ((payloadAddress p q).toNat+i)=p.memory.read8 ((payloadPointer p).toNat+i) := by
  have native:=allocation_copy_native p q hn hd
  have numbers:=payload_numbers p hn
  have endsp:=scratch_end p hn
  have outNat:(allocatedOut p).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have sp:(allocationInput p q).spVector.toNat=(scratch p).toNat:=congrArg UInt32.toNat hd.sp
  have source:(allocationInput p q).source=payloadPointer p:=hd.source
  have size:(allocationInput p q).size=count p:=hd.size
  have out:(allocationInput p q).outVector.toNat=(scratch p).toNat+48:=by change q.outVector.toNat=_;rw[hd.out];exact outNat
  have lower:=StateDecodeRaw.result_head_bound (allocationInput p q).toRaw native.vector.raw
  rw[allocation_head_eq p q hn hd] at lower
  have above:=hd.headAbove
  have pointer:(payloadAddress p q).toNat≥p.sp.toNat:=by exact Nat.le_trans above lower
  have sourceAbove:p.sp.toNat≤(payloadPointer p).toNat:=by have h:=hn.pointerAbove;omega
  have copied:=StateDecodeVectorCopy.final_original_bytes (allocationInput p q) native
    (by rw[sp,source];omega)
    (by rw[allocation_finish_eq p q hn hd,source];exact hheap)
    (by rw[source,size];exact hroot)
    (Or.inr (by rw[out,source];omega))
    (Or.inr (by rw[out];exact Nat.le_trans (by omega) pointer)) i (by rw[size];exact hi)
  have original: (takenPayloadMemory p).read8 ((payloadPointer p).toNat+i)=p.memory.read8 ((payloadPointer p).toNat+i):=
    (takenPayload_spec p hn).2.2.2 _ (by omega) (by omega)
  unfold allocatedMemory payloadAddress
  change (StateDecodeVectorCopy.finalMemory (allocationInput p q)).read8 ((StateDecodeVectorCopy.pointer (allocationInput p q)).toNat+i)=_
  rw[copied]
  rw[source]
  exact original
/-- Final allocated bytes equal the original payload snapshot. The final
caller output span is explicitly excluded from the allocated destination. -/
theorem final_payload_bytes (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(payloadPointer p).toNat)
    (hroot : (payloadPointer p).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(payloadPointer p).toNat)
    (hout : (payloadAddress p q).toNat+(count p).toNat≤p.out.toNat ∨p.out.toNat+16≤(payloadAddress p q).toNat)
    (i : Nat) (hi : i<(count p).toNat) :
    (finalMemory p q).read8 ((payloadAddress p q).toNat+i)=p.memory.read8 ((payloadPointer p).toNat+i) := by
  have native:=allocation_copy_native p q hn hd
  have lower:=StateDecodeRaw.result_head_bound (allocationInput p q).toRaw native.vector.raw
  rw[allocation_head_eq p q hn hd] at lower
  have above:=hd.headAbove
  have ptr:(payloadAddress p q).toNat≥p.sp.toNat:=Nat.le_trans above lower
  have descriptor:p.slice.toNat+8≤(payloadAddress p q).toNat:=Nat.le_trans hd.descriptorBeforeHead lower
  have a:=allocatedMemory_spec p q hn hd
  have add:(dropPayloadOut p).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have endsp:=scratch_end p hn
  have bound:(dropPayloadOut p).toNat+8≤(allocatedMemory p q).byteSize:=by rw[add,a.2.1];have h:=hn.spBound;omega
  have drop:=StateDecodeSlices.finalMemory_spec true (allocatedMemory p q) (dropPayloadOut p)
    (readI32 (allocatedMemory p q) p.slice.toNat) (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p) a.1 bound
  have no1:¬((dropPayloadOut p).toNat≤(payloadAddress p q).toNat+i ∧(payloadAddress p q).toNat+i<(dropPayloadOut p).toNat+4):=by rw[add];omega
  have no2:¬((dropPayloadOut p).toNat+4≤(payloadAddress p q).toNat+i ∧(payloadAddress p q).toNat+i<(dropPayloadOut p).toNat+8):=by rw[add];omega
  have df:(droppedMemory p q).read8 ((payloadAddress p q).toNat+i)=(allocatedMemory p q).read8 ((payloadAddress p q).toNat+i):=by
    unfold droppedMemory
    rw[drop.2.2.2]
    simp only[ite_eq_right no1,ite_eq_right no2]
  have of: (finalMemory p q).read8 ((payloadAddress p q).toNat+i)=(droppedMemory p q).read8 ((payloadAddress p q).toNat+i):=by
    apply Output.finalMemory_byte_frame (outputLayout p q) (output_native p q hn hd)
    · change _<p.out.toNat ∨p.out.toNat+16≤_
      rcases hout with h|h <;> omega
    · change _<p.slice.toNat ∨p.slice.toNat+8≤_
      exact Or.inr (by omega)
  exact of.trans (df.trans (allocated_payload_bytes p q hn hd hheap hroot i hi))

/-- A purely original geometry suffices: the caller output is below the
selected free node, hence below every allocated payload byte. -/
theorem final_payload_bytes_below_head (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AllocationDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(payloadPointer p).toNat)
    (hroot : (payloadPointer p).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(payloadPointer p).toNat)
    (hout : p.out.toNat+16≤(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat)
    (i : Nat) (hi : i<(count p).toNat) :
    (finalMemory p q).read8 ((payloadAddress p q).toNat+i)=p.memory.read8 ((payloadPointer p).toNat+i) := by
  have native:=allocation_copy_native p q hn hd
  have lower:=StateDecodeRaw.result_head_bound (allocationInput p q).toRaw native.vector.raw
  rw[allocation_head_eq p q hn hd] at lower
  exact final_payload_bytes p q hn hd hheap hroot (Or.inr (Nat.le_trans hout lower)) i hi
end WNear.Proofs.StateDecodePrefix
