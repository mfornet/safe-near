import Proofs.StateDecodeBorshIntervalFrame
import Proofs.StateDecodePrefixAllocatedFrame

/-! Scalar decoding and caller writes preserve the actual prefix allocation. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
theorem finalMemory_allocated_frame(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hstack:p.sp425.toNat≤j)
    (hout:j<p.out425.toNat ∨p.out425.toNat+44≤j)
    (hslice:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (finalMemory p q).read8 j=(StateDecodePrefix.allocatedMemory p.toPrefix q).read8 j:=by
  have n:=scratch_numbers p hn
  have sp:p.wrapperSP.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.childSP
  have out:p.wrapperOut.toNat=(scratch p).toNat+56:=by rw[hn.childOut];exact scratch_add p hn 56 (by omega)
  have inner:p.sp.toNat≤p.wrapperSP.toNat:=by
    rw[hn.prefixNative.childSP]
    change (p.wrapperSP-16).toNat≤p.wrapperSP.toNat
    rw[UInt32.toNat_sub]
    have lo:=hn.spLower
    have lt:=p.wrapperSP.toNat_lt
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have pref:=StateDecodePrefixWrapper.finalMemory_allocated_frame p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain j
    (by have lo:=hn.spLower;omega) (Or.inr (by rw[out];omega)) hslice
  exact (finalMemory_cached_byte_frame p q hn hd j hout).trans
    ((cachedMemory_interval p q hn hd j hstack hslice).trans pref)
end WNear.Proofs.StateDecodeBorsh
