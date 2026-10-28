import Proofs.StateDecodeBorshWrapperSlice
import Proofs.StateDecodeBorshPayload

/-! Allocated prefix bytes survive162 under original output-before-heap
geometry; all operational alias cases remain in the broader WP. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] decodedMemory finalMemory

theorem final_payload_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)
    (habove:p.sp162.toNat≤p.out162.toNat)
    (hout:p.out162.toNat+48≤(StateDecodeBorsh.originalHead q).toNat)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (hroot:(StateDecodePrefix.payloadPointer p.toPrefix).toNat+(count p).toNat≤q.allocator.toNat ∨
      q.allocator.toNat+4≤(StateDecodePrefix.payloadPointer p.toPrefix).toNat)
    (i:Nat)(hi:i<(count p).toNat):
    (finalMemory p q).read8 ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i)=
      p.memory.read8 (p.pointer.toNat+4+i):=by
  have sn:=scratch_numbers p hn
  have oldOut:p.out425.toNat=(scratch p).toNat+48:=by
    rw[hn.childOut];exact scratch_add p hn 48 (by omega)
  have childOut:p.out425.toNat+44≤(StateDecodeBorsh.originalHead q).toNat:=by omega
  have lower:=StateDecodeBorsh.payload_head_bound p.toBorsh q hn.child hd
  have old:=StateDecodeBorsh.final_payload_bytes p.toBorsh q hn.child hd hheap hroot childOut i hi
  have decoded:(decodedMemory p q).read8 ((StateDecodePrefix.payloadAddress p.toPrefix q).toNat+i)=
      p.memory.read8 (p.pointer.toNat+4+i):=by simpa only[decodedMemory] using old
  exact (finalMemory_decoded_byte_frame p q hn hd _ (by omega) (Or.inr (by omega))).trans decoded
end WNear.Proofs.StateDecodeBorshWrapper
