import Proofs.StateDecodePrefixAllocationBridge
import Proofs.StateDecodeVectorCopyIntervalFrame

/-! Descriptor readback through the actual accepted316 memory prefix. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 StateDecodeVectorCopy.finalMemory StateDecodeVector.finalMemory StateDecodeRaw.finalMemory

private theorem takenPayload_advanced_byte (p:Layout)(hn:Native p)(j:Nat)(hj:p.sp.toNat≤j):
    (takenPayloadMemory p).read8 j=(advancedMemory p).read8 j:=by
  have a:=advancedMemory_spec p hn
  have l:=lengthMemory_spec p hn
  have sa:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have sb:(takePayloadOut p).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have e:=scratch_end p hn
  have sp:=hn.spBound
  have lb:(lengthOut p).toNat+8≤(advancedMemory p).byteSize:=by rw[sa,a.2.1];omega
  have tb:(takePayloadOut p).toNat+8≤(lengthMemory p).byteSize:=by rw[sb,l.2.1];omega
  have ls:=StateDecodePrefixLeaves.recordMemory_spec (advancedMemory p) (lengthOut p) (count p) a.1 lb
  have ts:=StateDecodeSlices.finalMemory_spec false (lengthMemory p) (takePayloadOut p) (payloadPointer p) (remaining p) (count p) l.1 tb
  have noL0:¬((lengthOut p).toNat≤j ∧j<(lengthOut p).toNat+4):=by rw[sa];omega
  have noL4:¬((lengthOut p).toNat+4≤j ∧j<(lengthOut p).toNat+8):=by rw[sa];omega
  have noT0:¬((takePayloadOut p).toNat≤j ∧j<(takePayloadOut p).toNat+4):=by rw[sb];omega
  have noT4:¬((takePayloadOut p).toNat+4≤j ∧j<(takePayloadOut p).toNat+8):=by rw[sb];omega
  have first:(takenPayloadMemory p).read8 j=(lengthMemory p).read8 j:=by
    unfold takenPayloadMemory
    rw[ts.2.2.2]
    simp only[ite_eq_right noT0,ite_eq_right noT4]
  have second:(lengthMemory p).read8 j=(advancedMemory p).read8 j:=by
    unfold lengthMemory
    rw[ls.2.2.2]
    simp only[ite_eq_right noL0,ite_eq_right noL4]
  exact first.trans second

theorem takenPayload_descriptor (p:Layout)(hn:Native p):
    readI32 (takenPayloadMemory p) p.slice.toNat=payloadPointer p ∧
    readI32 (takenPayloadMemory p) (p.slice.toNat+4)=remaining p:=by
  have word (address:Nat)(ha:p.sp.toNat≤address):readI32 (takenPayloadMemory p) address=readI32 (advancedMemory p) address:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact takenPayload_advanced_byte p hn (address+i) (by omega)
  have h:=hn.sliceAbove
  exact ⟨(word p.slice.toNat h).trans (advanced_low p hn),(word (p.slice.toNat+4) (by omega)).trans (advanced_high p hn)⟩

/-- Every descriptor byte lies above the child stack/output and below the
original selected heap node, with the allocator root explicitly excluded. -/
theorem allocation_descriptor_geometry (p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AllocationDomain p q)(j:Nat)(hlo:p.slice.toNat≤j)(hhi:j<p.slice.toNat+8):
    q.spVector.toNat≤j ∧
    j<(AllocateSearch.head (AllocatePositive.searchLayout (allocationInput p q).toPositive)).toNat ∧
    (j<q.allocator.toNat ∨q.allocator.toNat+4≤j) ∧
    (j<q.outVector.toNat ∨q.outVector.toNat+12≤j):=by
  have se:=scratch_end p hn
  have sa:(allocatedOut p).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have sp:q.spVector.toNat=(scratch p).toNat:=congrArg UInt32.toNat hd.sp
  have out:q.outVector.toNat=(scratch p).toNat+48:=by rw[hd.out];exact sa
  have above:=hn.sliceAbove
  have before:=hd.descriptorBeforeHead
  have root:=hd.descriptorRootSep
  refine ⟨by omega,?_,?_,Or.inr (by omega)⟩
  · rw[allocation_head_eq p q hn hd];omega
  · rcases root with h|h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- The actual374 heap copy preserves the advanced caller descriptor.
Only the original descriptor/heap/root geometry is required. -/
theorem afterAllocation_descriptor (p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AllocationDomain p q):
    readI32 (StateDecodeVectorCopy.finalMemory (allocationInput p q)) p.slice.toNat=payloadPointer p ∧
    readI32 (StateDecodeVectorCopy.finalMemory (allocationInput p q)) (p.slice.toNat+4)=remaining p:=by
  have native:=allocation_copy_native p q hn hd
  have byte (j:Nat)(lo:p.slice.toNat≤j)(hi:j<p.slice.toNat+8):
      (StateDecodeVectorCopy.finalMemory (allocationInput p q)).read8 j=(takenPayloadMemory p).read8 j:=by
    have geo:=allocation_descriptor_geometry p q hn hd j lo hi
    have sp:(allocationInput p q).spVector.toNat≤j:=by simpa only[allocationInput] using geo.1
    have heap:j<(AllocateSearch.head (AllocatePositive.searchLayout (allocationInput p q).toPositive)).toNat:=geo.2.1
    have root:j<(allocationInput p q).allocator.toNat ∨(allocationInput p q).allocator.toNat+4≤j:=by simpa only[allocationInput] using geo.2.2.1
    have out:j<(allocationInput p q).outVector.toNat ∨(allocationInput p q).outVector.toNat+12≤j:=by simpa only[allocationInput] using geo.2.2.2
    have result:=StateDecodeVectorCopy.finalMemory_below_head (allocationInput p q) native j sp heap root out
    exact result
  have low:readI32 (StateDecodeVectorCopy.finalMemory (allocationInput p q)) p.slice.toNat=readI32 (takenPayloadMemory p) p.slice.toNat:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact byte (p.slice.toNat+i) (by omega) (by omega)
  have high:readI32 (StateDecodeVectorCopy.finalMemory (allocationInput p q)) (p.slice.toNat+4)=readI32 (takenPayloadMemory p) (p.slice.toNat+4):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact byte (p.slice.toNat+4+i) (by omega) (by omega)
  have before:=takenPayload_descriptor p hn
  exact ⟨low.trans before.1,high.trans before.2⟩

/-- The final real361 payload drop accepts the original decoded count. -/
theorem afterAllocation_split_le (p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AllocationDomain p q):
    (count p).toNat≤(readI32 (StateDecodeVectorCopy.finalMemory (allocationInput p q)) (p.slice.toNat+4)).toNat:=by
  rw[(afterAllocation_descriptor p q hn hd).2]
  exact (payload_numbers p hn).2.2.1
end WNear.Proofs.StateDecodePrefix
