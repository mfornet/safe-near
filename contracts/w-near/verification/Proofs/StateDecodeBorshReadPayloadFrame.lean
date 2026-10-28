import Proofs.StateDecodeBorshReadReadback

/-! The actual161 copies preserve bytes above SP and beyond its caller output. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem finalMemory_wrapped_byte_frame(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hsp:p.sp161.toNat≤j)(hout:p.out161.toNat+48≤j):
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
  rw[resultMemory,result.2.2.2 _ (Or.inr (by rw[o8];omega))]
  rw[acceptedMemory,second.2.2.2 _ (Or.inr (by rw[scratch_or4 p hn];omega))]
  rw[upperMemory,stored.2.2.2,ite_eq_right (by omega)]
  rw[scratchMemory,first.2.2.2 _ (Or.inr (by rw[a60];omega))]

theorem actual_finish_eq(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AllocationDomain p q):
    StateDecodeRaw.originalFinish (actualAllocation p q).toRaw=StateDecodeRaw.originalFinish q.toRaw:=by
  have head:=head_eq p q hn hd
  have hdr:=saved_word p q hn hd (AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat hd.headAbove
  unfold StateDecodeRaw.originalFinish AllocateSearch.finish
  rw[head]
  unfold Allocate.endWord
  exact congrArg (fun x:UInt32=>x &&&4294967292) hdr
end WNear.Proofs.StateDecodeBorshRead
