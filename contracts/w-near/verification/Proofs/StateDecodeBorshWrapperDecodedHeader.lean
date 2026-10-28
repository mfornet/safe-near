import Proofs.StateDecodeBorshWrapperResult

namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 finalMemory decodedMemory StateDecodeBorsh.finalMemory
attribute [local irreducible] StateDecodePrefix.payloadAddress StateDecodePrefix.allocationInput
attribute [local irreducible] StateDecodeBorsh.count count StateDecodeBorsh.widePointer StateDecodeBorsh.wideLength
private theorem read32_copy(first second:Memory)(out source:Nat)
    (h:∀i,i<4→first.read8 (out+i)=second.read8 (source+i)):
    readI32 first out=readI32 second source:=by
  have zero:first.read8 out=second.read8 source:=by simpa only[Nat.add_zero] using h 0 (by omega)
  simp[readI32,List.range_succ,h,zero]

/-- The complete162 memory record represents the original model header. -/
theorem decoded_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(habove:p.sp162.toNat≤p.out162.toNat)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+29≤q.allocator.toNat ∨
      q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out162.toNat+48≤(StateDecodeBorsh.originalHead q).toNat):
    StateDecodeBorsh.DecodedAt (finalMemory p q) p.out162.toNat state:=by
  have sn:=scratch_numbers p hn
  have address:p.out425.toNat=(scratch p).toNat+48:=by rw[hn.childOut];exact scratch_add p hn 48 (by omega)
  have childOut:p.out425.toNat+44≤(StateDecodeBorsh.originalHead q).toNat:=by omega
  have old:=StateDecodeBorsh.decoded_header p.toBorsh q hn.child hd state hw h hheap hroot childOut
  have decoded:StateDecodeBorsh.DecodedAt (decodedMemory p q) p.out425.toNat state:=by
    simpa only[decodedMemory] using old
  rcases decoded with ⟨_,supply,usage,x,hx,capacity,length,bound,byte⟩
  have vector:=StateDecodeBorsh.final_vector_record p.toBorsh q hn.child hd
  have pointer:readI32 (decodedMemory p q) (p.out425.toNat+32)=StateDecodePrefix.payloadAddress p.toPrefix q:=by
    simpa only[decodedMemory] using vector.1
  have xe:x=StateDecodePrefix.payloadAddress p.toPrefix q:=hx.symm.trans pointer
  have lower:=StateDecodeBorsh.payload_head_bound p.toBorsh q hn.child hd
  rw[←xe] at lower
  have words(offset:Nat)(ho:offset=32 ∨offset=36 ∨offset=40):
      readI32 (finalMemory p q) (p.out162.toNat+offset)=readI32 (decodedMemory p q) (p.out425.toNat+offset):=by
    apply read32_copy
    intro i hi
    have b:=final_record_bytes p q hn hd habove (offset-8+i) (by rcases ho with rfl|rfl|rfl <;> omega)
    have a:p.out162.toNat+8+(offset-8+i)=p.out162.toNat+offset+i:=by rcases ho with rfl|rfl|rfl <;> omega
    have z:(scratch p).toNat+56+(offset-8+i)=p.out425.toNat+offset+i:=by rw[address];rcases ho with rfl|rfl|rfl <;> omega
    simpa only[a,z] using b
  have word64:=(final_record_words p q hn hd habove).1
  have supplyNew:TotalSupply.U128At (finalMemory p q) (p.out162.toNat+8) state.totalSupply:=by
    unfold TotalSupply.U128At at *
    have a:p.out162.toNat+8+8=p.out162.toNat+16:=by omega
    have b:p.out425.toNat+8+8=p.out425.toNat+16:=by omega
    rw[b,address] at supply
    rw[a,word64 8 (by omega),word64 16 (by omega)]
    exact supply
  have usageNew:readI64 (finalMemory p q) (p.out162.toNat+24)=UInt64.ofNat state.accountStorageUsage:=by
    rw[address] at usage
    exact (word64 24 (by omega)).trans usage
  have shapeD:=decodedMemory_spec p q hn hd
  have shapeF:=finalMemory_spec p q hn hd
  have payload:(finalMemory p q).read8 x.toNat=97:=
    (finalMemory_decoded_byte_frame p q hn hd x.toNat (by omega) (Or.inr (by omega))).trans byte
  exact ⟨finalMemory_tag p q hn hd,supplyNew,usageNew,x,(words 32 (by omega)).trans hx,
    (words 36 (by omega)).trans capacity,(words 40 (by omega)).trans length,by rw[shapeD.2.1] at bound;rw[shapeF.2.1];exact bound,payload⟩

theorem callAfter_decoded_header(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (habove:p.sp162.toNat≤p.out162.toNat)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+29≤q.allocator.toNat ∨q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hout:p.out162.toNat+48≤(StateDecodeBorsh.originalHead q).toNat):
    (callAfter cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q) ∧
    StateDecodeBorsh.DecodedAt (finalMemory p q) p.out162.toNat state:=
  ⟨callAfter_memory cfg s p q hn hd hm,decoded_header p q hn hd habove state hw h hheap hroot hout⟩
end WNear.Proofs.StateDecodeBorshWrapper
