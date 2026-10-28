import Proofs.StateDecodeBorshPayloadFrame
import Proofs.StateDecodePrefixPayload
import Proofs.StateDecodePrefixWrapperRecord

/-! Actual425 retains the allocated account-prefix bytes. The additional
separations refer to the original selected heap node, source, and caller output. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

def originalHead(q:StateDecodeVectorCopy.Layout):=AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)

theorem payload_head_bound(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (originalHead q).toNat≤(StateDecodePrefix.payloadAddress p.toPrefix q).toNat:=by
  have native:=StateDecodePrefix.allocation_copy_native p.toPrefix q hn.prefixNative.child hd.toAllocationDomain
  have lower:=StateDecodeRaw.result_head_bound (StateDecodePrefix.allocationInput p.toPrefix q).toRaw native.vector.raw
  rw[StateDecodePrefix.allocation_head_eq p.toPrefix q hn.prefixNative.child hd.toAllocationDomain] at lower
  exact lower

theorem prefix_payload_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out425.toNat+44≤(originalHead q).toNat)
    (i:Nat)(hi:i<(count p).toNat):
    (prefixMemory p q).read8 ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i)=
      p.memory.read8 ((StateDecodePrefix.payloadPointer p.toPrefix).toNat+i):=by
  have lower:=payload_head_bound p q hn hd
  have n:=scratch_numbers p hn
  have outAbove:=hn.outAbove
  have wrapperOut:p.wrapperOut.toNat=(scratch p).toNat+56:=by rw[hn.childOut];exact scratch_add p hn 56 (by omega)
  have small:(StateDecodePrefixWrapper.scratch p.toPrefixWrapper).toNat=(scratch p).toNat-16:=by
    unfold StateDecodePrefixWrapper.scratch
    rw[hn.childSP,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have lo:=hn.spLower
    have lt:=(scratch p).toNat_lt
    omega
  have childOut:p.out.toNat+16≤(originalHead q).toNat:=by rw[hn.prefixNative.childOut,small];omega
  have bytes:=StateDecodePrefix.final_payload_bytes_below_head p.toPrefix q hn.prefixNative.child hd.toAllocationDomain hheap hroot childOut i hi
  have frame:(prefixMemory p q).read8 ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i)=
      (StateDecodePrefix.finalMemory p.toPrefix q).read8 ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i):=by
    apply StateDecodePrefixWrapper.Tail.finalMemory_byte_frame (StateDecodePrefixWrapper.tailLayout p.toPrefixWrapper q)
      (StateDecodePrefixWrapper.tail_native p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain)
    change _<p.wrapperOut.toNat ∨p.wrapperOut.toNat+16≤_
    right;rw[wrapperOut];omega
  exact frame.trans bytes

theorem final_payload_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out425.toNat+44≤(originalHead q).toNat)
    (i:Nat)(hi:i<(count p).toNat):
    (finalMemory p q).read8 ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i)=
      p.memory.read8 (p.pointer.toNat+4+i):=by
  have lower:=payload_head_bound p q hn hd
  have descriptor:p.slice.toNat+8≤(originalHead q).toNat:=hd.descriptorBeforeHead
  have above:=hn.outAbove
  have frame:=finalMemory_byte_above p q hn hd ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i)
    (by omega) (by omega) (by omega)
  have bytes:=prefix_payload_bytes p q hn hd hheap hroot hout i hi
  have pointer:=(StateDecodePrefix.payload_numbers p.toPrefix hn.prefixNative.child).1
  rw[pointer] at bytes
  exact frame.trans bytes
end WNear.Proofs.StateDecodeBorsh
