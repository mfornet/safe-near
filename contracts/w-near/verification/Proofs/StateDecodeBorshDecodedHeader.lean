import Proofs.StateDecodeBorshHeader
import Proofs.StateDecodeBorshVectorValues
import Proofs.StateDecodeBorshPayload

/-! The complete successful425 record represents the original model header.
DecodedAt is an output predicate proved here, never a decoder premise. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 finalMemory StateDecodePrefix.allocationInput StateDecodePrefix.payloadAddress StateDecodeVectorCopy.pointer StateDecodePrefix.takenPayloadMemory

/-- The exact successful guest record: supply, storage usage, and the allocated
one-byte accounts-prefix vector, with a valid payload byte. Padding is unconstrained. -/
def DecodedAt(memory:Memory)(out:Nat)(state:WNear.State):Prop:=
  readI32 memory out=0 ∧TotalSupply.U128At memory (out+8) state.totalSupply ∧
  readI64 memory (out+24)=UInt64.ofNat state.accountStorageUsage ∧
  ∃pointer:UInt32,readI32 memory (out+32)=pointer ∧readI32 memory (out+36)=1 ∧
    readI32 memory (out+40)=1 ∧pointer.toNat+1≤memory.byteSize ∧memory.read8 pointer.toNat=97

private theorem span_transport(address size count before after:Nat)
    (h:address+size≤before)(hs:size=count)(hb:before=after):address+count≤after:=by omega

theorem payload_bound(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (StateDecodePrefix.payloadAddress p.toPrefix q).toNat+(count p).toNat≤(finalMemory p q).byteSize:=by
  have native:=StateDecodePrefix.allocation_copy_native p.toPrefix q hn.prefixNative.child hd.toAllocationDomain
  have bounds:=StateDecodeVectorCopy.copy_bounds (StateDecodePrefix.allocationInput p.toPrefix q) native
  have size:(StateDecodePrefix.allocationInput p.toPrefix q).size=count p:=by
    simp only[StateDecodePrefix.allocationInput]
    exact hd.size
  have mem:(StateDecodePrefix.allocationInput p.toPrefix q).memory=StateDecodePrefix.takenPayloadMemory p.toPrefix:=by simp only[StateDecodePrefix.allocationInput]
  have original:=(StateDecodePrefix.takenPayload_spec p.toPrefix hn.prefixNative.child).2.1
  have endSize:(finalMemory p q).byteSize=p.memory.byteSize:=(finalMemory_spec p q hn hd).2.1
  have bytes:=bounds.2.1.trans ((congrArg Memory.byteSize mem).trans (original.trans endSize.symm))
  have transported:=span_transport _ _ _ _ _ bounds.2.2.2.2.1 (congrArg UInt32.toNat size) bytes
  simpa only[StateDecodePrefix.payloadAddress] using transported

private theorem byte_zero(m n:Memory)(source destination:Nat)
    (h:n.read8 (destination+0)=m.read8 (source+0))(b:m.read8 source=97):n.read8 destination=97:=by
  simpa only[Nat.add_zero] using h.trans b

theorem decoded_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+29≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out425.toNat+44≤(originalHead q).toNat):
    DecodedAt (finalMemory p q) p.out425.toNat state:=by
  have one:=header_count p state hw h
  have num:(count p).toNat=1:=by rw[one];rfl
  have ptr:=(StateDecodePrefix.payload_numbers p.toPrefix hn.prefixNative.child).1
  have wide:=header_numbers p hn
  have heap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat:=by rw[ptr] at hheap;omega
  have root:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat:=by
    rw[ptr] at hroot
    rcases hroot with h|h <;> omega
  have scalars:=finalMemory_header_scalars p q hn hd state hw h heap root
  have vector:=final_vector_record p q hn hd
  rw[one] at vector
  have bound:=payload_bound p q hn hd
  rw[num] at bound
  have rootPayload:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+(count p).toNat≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat:=by
    rcases hroot with h|h
    · left;rw[num];omega
    · exact Or.inr h
  have byte:=final_payload_bytes p q hn hd hheap rootPayload hout 0 (by rw[num];omega)
  have original:=StateDecodePrefix.header_payload_byte p.toPrefix hn.prefixNative.child state hw h
  have addr:(StateDecodePrefix.payloadPointer p.toPrefix).toNat=p.pointer.toNat+4:=ptr
  rw[addr] at original
  refine ⟨scalars.1,scalars.2.1,scalars.2.2,StateDecodePrefix.payloadAddress p.toPrefix q,
    vector.1,vector.2.1,vector.2.2,bound,byte_zero _ _ _ _ byte original⟩
end WNear.Proofs.StateDecodeBorsh
