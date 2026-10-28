import Proofs.StateDecodeVectorIntervalFrame
import Proofs.StateDecodeVectorCopyMemory

/-! Descriptor bytes below the original selected heap node survive actual374.
The copy's allocated destination is proved above that node, not assumed. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] writeI32 copiedMemory

theorem finalMemory_below_head (p:Layout)(hn:Native p)(j:Nat)
    (hstack:p.spVector.toNat≤j)
    (hheap:j<(AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat)
    (hroot:j<p.allocator.toNat ∨p.allocator.toNat+4≤j)
    (hout:j<p.outVector.toNat ∨p.outVector.toNat+12≤j):
    (finalMemory p).read8 j=p.memory.read8 j:=by
  have vector:=StateDecodeVector.finalMemory_interval_frame p.toVector hn.vector j hstack (Or.inl hheap) hroot hout
  have destination:=StateDecodeRaw.result_head_bound p.toRaw hn.vector.raw
  have before:j<(pointer p).toNat:=by change _≤(pointer p).toNat at destination;omega
  have copy: (copiedMemory p).read8 j=(StateDecodeVector.finalMemory p.toVector).read8 j:=
    (copiedMemory_spec p hn).2.2.2 j (Or.inl before)
  have last: (finalMemory p).read8 j=(copiedMemory p).read8 j:=
    (finalMemory_spec p hn).2.2.2.2 j (by rcases hout with h|h <;> omega)
  exact last.trans (copy.trans vector)
end WNear.Proofs.StateDecodeVectorCopy
