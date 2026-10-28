import Proofs.StateDecodeBorshWrapperHeader
import Proofs.StateDecodeBorshSlice

/-! Original descriptor separation preserves425's exhausted-header slice
through both actual162 copies and its final output stores. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
attribute [local irreducible] decodedMemory firstMemory packedMemory secondMemory finalMemory packedValue

/-- Bytes above original SP and outside the48-byte caller output retain425's
post-state. This states a checked footprint, without source/output snapshot assumptions. -/
theorem finalMemory_decoded_byte_frame(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(j:Nat)(hsp:p.sp162.toNat≤j)
    (hout:j<p.out162.toNat ∨p.out162.toNat+48≤j):
    (finalMemory p q).read8 j=(decodedMemory p q).read8 j:=by
  have sn:=scratch_numbers p hn
  have bounds:=hn.outputBound
  have a12:(scratch p+12).toNat=(scratch p).toNat+12:=scratch_add p hn 12 (by omega)
  have o8:(p.out162+8).toNat=p.out162.toNat+8:=output_add p hn 8 (by omega)
  have o12:(p.out162+12).toNat=p.out162.toNat+12:=output_add p hn 12 (by omega)
  have sd:=decodedMemory_spec p q hn hd
  have sf:=firstMemory_spec p q hn hd
  have sp:=packedMemory_spec p q hn hd
  have ss:=secondMemory_spec p q hn hd
  have tag:=writeI32_spec (secondMemory p q) p.out162.toNat 0 ss.1 (by rw[ss.2.1];omega)
  have second:=ForwardCopyMemory.spec (packedMemory p q) (p.out162+12).toNat (scratch p+12).toNat 36 sp.1 (second_copy_bounds p q hn hd).1
  have packed:=writeI32_spec (firstMemory p q) (p.out162+8).toNat (UInt32.ofNat ((packedValue p q >>>32).toNat)) sf.1 (by rw[o8,sf.2.1];omega)
  have first:=ForwardCopyMemory.spec (decodedMemory p q) (scratch p+12).toNat ((scratch p+48)+12).toNat 36 sd.1 (first_copy_bounds p q hn hd).1
  rw[finalMemory,tag.2.2.2,ite_eq_right (by omega)]
  rw[secondMemory,second.2.2.2 j (by rcases hout with h|h;exact Or.inl (by omega);exact Or.inr (by omega))]
  rw[packedMemory,packed.2.2.2,ite_eq_right (by omega)]
  rw[firstMemory,first.2.2.2 j (Or.inr (by omega))]

/-- The actual remaining descriptor after162, conditional only on original
input/output geometry and original29-byte input length. -/
theorem finalMemory_exhausted_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)
    (hs:p.sp162.toNat≤p.slice.toNat)
    (hout:p.out162.toNat+48≤p.slice.toNat ∨p.slice.toNat+8≤p.out162.toNat)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hl:p.length=29):
    readI32 (finalMemory p q) p.slice.toNat=p.pointer+29 ∧
    readI32 (finalMemory p q) (p.slice.toNat+4)=0:=by
  have sn:=scratch_numbers p hn
  have childOut:p.out425.toNat=(scratch p).toNat+48:=by
    rw[hn.childOut];exact scratch_add p hn 48 (by omega)
  have childSep:p.out425.toNat+44≤p.slice.toNat ∨p.slice.toNat+8≤p.out425.toNat:=by
    left;omega
  have child:=StateDecodeBorsh.finalMemory_exhausted_header p.toBorsh q hn.child hd childSep
    (StateDecodeBorsh.header_count p.toBorsh state hw h) hl
  have old:readI32 (decodedMemory p q) p.slice.toNat=p.pointer+29 ∧
    readI32 (decodedMemory p q) (p.slice.toNat+4)=0:=by simpa only[decodedMemory] using child
  have word(address:Nat)(ha:p.slice.toNat≤address)(hb:address+4≤p.slice.toNat+8):
      readI32 (finalMemory p q) address=readI32 (decodedMemory p q) address:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact finalMemory_decoded_byte_frame p q hn hd (address+i) (by omega)
      (by rcases hout with h|h;exact Or.inr (by omega);exact Or.inl (by omega))
  exact ⟨(word _ (by omega) (by omega)).trans old.1,(word _ (by omega) (by omega)).trans old.2⟩
end WNear.Proofs.StateDecodeBorshWrapper
