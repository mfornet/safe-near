import Proofs.StateDecodeBorshReadPayloadFrame
import Proofs.StateDecodeBorshReadHeader
import Proofs.StateDecodeBorshWrapperDecodedHeader

/-! The actual161 record represents the original model header. All source,
heap and output separations are stated on the original input memory. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
attribute [local irreducible] wrappedMemory finalMemory StateDecodePrefix.payloadAddress StateDecodePrefix.allocationInput

private theorem read32_eq(m n:Memory)(a b:Nat)(h:∀i,i<4→m.read8 (a+i)=n.read8 (b+i)):
    readI32 m a=readI32 n b:=by
  have zero:=h 0 (by omega)
  simp only[Nat.add_zero] at zero
  simp[readI32,List.range_succ,h,zero]

theorem wrapped_pointer(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    readI32 (wrappedMemory p q) (p.out162.toNat+32)=
      StateDecodePrefix.payloadAddress (actualWrapper p).toPrefix (actualAllocation p q):=by
  have native:=wrapper_native p hn
  have domain:=accepted_domain p q hn hd
  have geo:=stack_geometry p hn
  have habove:(actualWrapper p).sp162.toNat≤(actualWrapper p).out162.toNat:=by
    change p.sp162.toNat≤p.out162.toNat;omega
  have child:readI32 (StateDecodeBorshWrapper.decodedMemory (actualWrapper p) (actualAllocation p q)) (p.out425.toNat+32)=
      StateDecodePrefix.payloadAddress (actualWrapper p).toPrefix (actualAllocation p q):=
    (StateDecodeBorsh.final_vector_record (actualWrapper p).toBorsh (actualAllocation p q) native.child domain).1
  have address:p.out425.toNat=(StateDecodeBorshWrapper.scratch (actualWrapper p)).toNat+48:=by
    have a:(StateDecodeBorshWrapper.scratch (actualWrapper p)+48).toNat=(StateDecodeBorshWrapper.scratch (actualWrapper p)).toNat+48:=
      StateDecodeBorshWrapper.scratch_add (actualWrapper p) native 48 (by omega)
    have childOut:p.out425=StateDecodeBorshWrapper.scratch (actualWrapper p)+48:=native.childOut
    rw[childOut,a]
  have eq:readI32 (wrappedMemory p q) (p.out162.toNat+32)=
      readI32 (StateDecodeBorshWrapper.decodedMemory (actualWrapper p) (actualAllocation p q)) (p.out425.toNat+32):=by
    apply read32_eq
    intro i hi
    have b:=StateDecodeBorshWrapper.final_record_bytes (actualWrapper p) (actualAllocation p q) native domain habove (24+i) (by omega)
    have a:(actualWrapper p).out162.toNat+8+(24+i)=p.out162.toNat+32+i:=by change p.out162.toNat+8+(24+i)=_;omega
    have z:(StateDecodeBorshWrapper.scratch (actualWrapper p)).toNat+56+(24+i)=p.out425.toNat+32+i:=by rw[address];omega
    rw[a,z] at b
    unfold wrappedMemory;exact b
  exact eq.trans child

theorem wrapped_decoded_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+29≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out161.toNat+48≤(StateDecodeBorsh.originalHead q).toNat)(habove:p.sp161.toNat≤p.out161.toNat):
    StateDecodeBorsh.DecodedAt (wrappedMemory p q) p.out162.toNat state:=by
  have native:=wrapper_native p hn
  have domain:=accepted_domain p q hn hd
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have head:StateDecodeBorsh.originalHead (actualAllocation p q)=StateDecodeBorsh.originalHead q:=head_eq p q hn hd.toAllocationDomain
  have heap:(StateDecodeRaw.originalFinish (actualAllocation p q).toRaw).toNat+8≤
      (StateDecodePrefix.payloadPointer (actualWrapper p).toPrefix).toNat:=by
    rw[actual_finish_eq p q hn hd.toAllocationDomain]
    exact hheap
  have root:(StateDecodePrefix.payloadPointer (actualWrapper p).toPrefix).toNat+29≤(actualAllocation p q).allocator.toNat ∨
      (actualAllocation p q).allocator.toNat+4≤(StateDecodePrefix.payloadPointer (actualWrapper p).toPrefix).toNat:=hroot
  have out:(actualWrapper p).out162.toNat+48≤(StateDecodeBorsh.originalHead (actualAllocation p q)).toNat:=by
    rw[head];change p.out162.toNat+48≤_;omega
  unfold wrappedMemory
  exact StateDecodeBorshWrapper.decoded_header (actualWrapper p) (actualAllocation p q) native domain
    (by change p.sp162.toNat≤p.out162.toNat;omega) state hw (setup_header p hn state h) heap root out

theorem decoded_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+29≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out161.toNat+48≤(StateDecodeBorsh.originalHead q).toNat)(habove:p.sp161.toNat≤p.out161.toNat):
    StateDecodeBorsh.DecodedAt (finalMemory p q) p.out161.toNat state:=by
  have old:=wrapped_decoded_header p q hn hd state hw h hheap hroot hout habove
  rcases old with ⟨_,supply,usage,x,hx,capacity,length,bound,byte⟩
  have pointer:=wrapped_pointer p q hn hd
  have xe:x=StateDecodePrefix.payloadAddress (actualWrapper p).toPrefix (actualAllocation p q):=hx.symm.trans pointer
  have lower:=StateDecodeBorsh.payload_head_bound (actualWrapper p).toBorsh (actualAllocation p q) (borsh_native p hn) (accepted_domain p q hn hd)
  have head:StateDecodeBorsh.originalHead (actualAllocation p q)=StateDecodeBorsh.originalHead q:=head_eq p q hn hd.toAllocationDomain
  rw[head,←xe] at lower
  have words:=final_record_words p q hn hd habove
  have geo:=stack_geometry p hn
  have source:p.out162.toNat=(scratch p).toNat+96:=geo.2.2.2.2.2.2.2.1
  have supplyNew:TotalSupply.U128At (finalMemory p q) (p.out161.toNat+8) state.totalSupply:=by
    unfold TotalSupply.U128At at *
    have a:p.out161.toNat+8+8=p.out161.toNat+16:=by omega
    have b:p.out162.toNat+8+8=p.out162.toNat+16:=by omega
    rw[b,source] at supply
    rw[a,words.1 8 (by omega),words.1 16 (by omega)]
    exact supply
  have usageNew:readI64 (finalMemory p q) (p.out161.toNat+24)=UInt64.ofNat state.accountStorageUsage:=by
    rw[source] at usage
    exact (words.1 24 (by omega)).trans usage
  have wd:=wrappedMemory_spec p q hn hd
  have fs:=finalMemory_spec p q hn hd
  have pointerNew:readI32 (finalMemory p q) (p.out161.toNat+32)=x:=by
    rw[source] at hx
    exact (words.2 32 (by omega)).trans hx
  have capacityNew:readI32 (finalMemory p q) (p.out161.toNat+36)=1:=by
    rw[source] at capacity
    exact (words.2 36 (by omega)).trans capacity
  have lengthNew:readI32 (finalMemory p q) (p.out161.toNat+40)=1:=by
    rw[source] at length
    exact (words.2 40 (by omega)).trans length
  have payload:(finalMemory p q).read8 x.toNat=97:=
    (finalMemory_wrapped_byte_frame p q hn hd x.toNat (by omega) (by omega)).trans byte
  refine ⟨finalMemory_tag p q hn hd,supplyNew,usageNew,x,pointerNew,capacityNew,lengthNew,?_,payload⟩
  exact Nat.le_trans bound (Nat.le_of_eq (wd.2.1.trans fs.2.1.symm))
end WNear.Proofs.StateDecodeBorshRead
