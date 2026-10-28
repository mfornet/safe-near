import Proofs.StateDecodeBorshIntervalFrame
import Proofs.StateDecodeBorshWrapperSlice

/-! The real162 copies preserve original bytes below the selected free block,
above its stack and outside the original caller-output/descriptor spans. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_below_head(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(j:Nat)(hstack:p.sp162.toNat≤j)
    (hheap:j<(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat)
    (hroot:j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hout:j<p.out162.toNat ∨p.out162.toNat+48≤j)
    (hslice:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (finalMemory p q).read8 j=p.memory.read8 j:=by
  have sn:=scratch_numbers p hn
  have sp:p.sp425.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.childSP
  have out:p.out425.toNat=(scratch p).toNat+48:=by rw[hn.childOut];exact scratch_add p hn 48 (by omega)
  have child:=StateDecodeBorsh.finalMemory_below_head p.toBorsh q hn.child hd j
    (by rw[sp];omega) hheap hroot (Or.inr (by rw[out];omega)) hslice
  exact (finalMemory_decoded_byte_frame p q hn hd j hstack hout).trans child
end WNear.Proofs.StateDecodeBorshWrapper
