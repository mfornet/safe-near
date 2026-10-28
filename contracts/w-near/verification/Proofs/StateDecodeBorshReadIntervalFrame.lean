import Proofs.StateDecodeBorshReadPayloadFrame
import Proofs.StateDecodeBorshWrapperIntervalFrame

/-! The actual161 copies preserve bytes above SP and beyond its caller output. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_wrapped_interval(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hsp:p.sp161.toNat≤j)(hout:j<p.out161.toNat ∨p.out161.toNat+48≤j):
    (finalMemory p q).read8 j=(wrappedMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have wd:=wrappedMemory_spec p q hn hd
  have sc:=scratchMemory_spec p q hn hd
  have up:=upperMemory_spec p q hn hd
  have ac:=acceptedMemory_spec p q hn hd
  have rs:=resultMemory_spec p q hn hd
  have a60:(scratch p+60).toNat=(scratch p).toNat+60:=scratch_add p hn 60 (by omega)
  have o8:(p.out161+8).toNat=p.out161.toNat+8:=by
    have b:=hn.outBound;have w:=hn.width
    rw[UInt32.toNat_add];simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have first:=ForwardCopyMemory.spec (wrappedMemory p q) (scratch p+60).toNat (scratch p+108).toNat 36 wd.1 (first_copy_bounds p q hn hd).1
  have stored:=writeI32_spec (scratchMemory p q) ((scratch p).toNat+16) (UInt32.ofNat ((packedValue p q>>>32).toNat)) sc.1 (by rw[sc.2.1];omega)
  have second:=ForwardCopyMemory.spec (upperMemory p q) ((scratch p+16)|||4).toNat (scratch p+60).toNat 36 up.1 (accepted_copy_bounds p q hn hd).1
  have result:=ForwardCopyMemory.spec (acceptedMemory p q) (p.out161+8).toNat (scratch p+16).toNat 40 ac.1 (result_copy_bounds p q hn hd).1
  have b:=hn.outBound
  have tag:=writeI32_spec (resultMemory p q) p.out161.toNat 0 rs.1 (by rw[rs.2.1];omega)
  rw[finalMemory,tag.2.2.2,ite_eq_right (by omega)]
  rw[resultMemory,result.2.2.2 _ (by rw[o8];rcases hout with h|h;exact Or.inl (by omega);exact Or.inr (by omega))]
  rw[acceptedMemory,second.2.2.2 _ (Or.inr (by rw[scratch_or4 p hn];omega))]
  rw[upperMemory,stored.2.2.2,ite_eq_right (by omega)]
  rw[scratchMemory,first.2.2.2 _ (Or.inr (by rw[a60];omega))]


theorem finalMemory_below_head(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hstack:p.sp161.toNat≤j)
    (hheap:j<(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat)
    (hroot:j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hout:j<p.out161.toNat ∨p.out161.toNat+48≤j):
    (finalMemory p q).read8 j=p.memory.read8 j:=by
  have n:=scratch_numbers p hn
  have geo:=stack_geometry p hn
  have heap:j<(AllocateSearch.head (AllocatePositive.searchLayout (actualAllocation p q).toPositive)).toNat:=by
    rw[head_eq p q hn hd.toAllocationDomain];exact hheap
  have child:=StateDecodeBorshWrapper.finalMemory_below_head (actualWrapper p) (actualAllocation p q)
    (wrapper_native p hn) (accepted_domain p q hn hd) j (by change p.sp162.toNat≤j;omega)
    heap hroot (by change j<p.out162.toNat ∨p.out162.toNat+48≤j;right;omega)
    (by change j<p.slice.toNat ∨p.slice.toNat+8≤j;right;omega)
  exact (finalMemory_wrapped_interval p q hn hd j hstack hout).trans
    (child.trans (setupMemory_byte_frame p hn j (Or.inr (by omega))))
end WNear.Proofs.StateDecodeBorshRead
