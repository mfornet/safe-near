import Proofs.StateDecodeBorshAllocatedFrame
import Proofs.StateDecodeBorshWrapperSlice

/-! The actual162 copies frame the actual prefix allocation. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
theorem finalMemory_allocated_frame(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(j:Nat)(hstack:p.sp162.toNat≤j)
    (hout:j<p.out162.toNat ∨p.out162.toNat+48≤j)
    (hslice:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (finalMemory p q).read8 j=(StateDecodePrefix.allocatedMemory p.toPrefix q).read8 j:=by
  have sn:=scratch_numbers p hn
  have sp:p.sp425.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.childSP
  have out:p.out425.toNat=(scratch p).toNat+48:=by rw[hn.childOut];exact scratch_add p hn 48 (by omega)
  have child:=StateDecodeBorsh.finalMemory_allocated_frame p.toBorsh q hn.child hd j
    (by rw[sp];omega) (Or.inr (by rw[out];omega)) hslice
  exact (finalMemory_decoded_byte_frame p q hn hd j hstack hout).trans child
end WNear.Proofs.StateDecodeBorshWrapper
