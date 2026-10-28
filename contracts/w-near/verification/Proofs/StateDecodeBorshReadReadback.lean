import Proofs.StateDecodeBorshReadMemoryNative
import Proofs.AllocateLayoutWrapperReadback

/-! Canonical161 output reconstruction. The original caller output is above SP;
every inner copy remains the deployed sequential forward copy. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
attribute [local irreducible] wrappedMemory scratchMemory upperMemory acceptedMemory resultMemory finalMemory packedValue

private theorem shifted_byte(value:UInt64)(i:Nat)(hi:i<4):
    UInt8.ofNat ((UInt32.ofNat ((value>>>32).toNat)).toNat >>>(8*i))=
      UInt8.ofNat (value.toNat >>>(8*(4+i))):=by
  apply UInt8.toNat_inj.mp
  have cases:i=0∨i=1∨i=2∨i=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl <;> simp[UInt64.toNat_shiftRight,Nat.shiftRight_eq_div_pow] <;> omega

private theorem packed_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(i:Nat)(hi:i<4):
    UInt8.ofNat ((UInt32.ofNat ((packedValue p q>>>32).toNat)).toNat >>>(8*i))=
      (wrappedMemory p q).read8 ((scratch p).toNat+104+i):=by
  rw[shifted_byte _ i hi,packedValue,AllocateLayoutWrapperReadback.readI64_byte _ _ (4+i) (by omega)]
  congr 1;omega

theorem accepted_record_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (i:Nat)(hi:i<40):
    (acceptedMemory p q).read8 ((scratch p).toNat+16+i)=
      (wrappedMemory p q).read8 ((scratch p).toNat+104+i):=by
  have n:=scratch_numbers p hn
  have a60:(scratch p+60).toNat=(scratch p).toNat+60:=scratch_add p hn 60 (by omega)
  have a108:(scratch p+108).toNat=(scratch p).toNat+108:=scratch_add p hn 108 (by omega)
  have wrapped:=wrappedMemory_spec p q hn hd
  have scratchShape:=scratchMemory_spec p q hn hd
  have upper:=upperMemory_spec p q hn hd
  have stored:=writeI32_spec (scratchMemory p q) ((scratch p).toNat+16) (UInt32.ofNat ((packedValue p q>>>32).toNat)) scratchShape.1 (by rw[scratchShape.2.1];omega)
  by_cases low:i<4
  · have copied:=ForwardCopyMemory.spec (upperMemory p q) ((scratch p+16)|||4).toNat (scratch p+60).toNat 36 upper.1 (accepted_copy_bounds p q hn hd).1
    rw[acceptedMemory,copied.2.2.2 _ (Or.inl (by rw[scratch_or4 p hn];omega)),upperMemory,stored.2.2.2,ite_eq_left (by omega)]
    have idx:(scratch p).toNat+16+i-((scratch p).toNat+16)=i:=by omega
    rw[idx];exact packed_bytes p q i low
  · have second:=ForwardCopyMemory.copied_bytes (upperMemory p q) ((scratch p+16)|||4).toNat (scratch p+60).toNat 36 upper.1 (accepted_copy_bounds p q hn hd).1
      (Or.inl (by rw[scratch_or4 p hn,a60];omega)) (i-4) (by omega)
    have dest:((scratch p+16)|||4).toNat+(i-4)=(scratch p).toNat+16+i:=by rw[scratch_or4 p hn];omega
    rw[dest] at second
    rw[acceptedMemory,second,upperMemory,stored.2.2.2,ite_eq_right (by rw[a60];omega)]
    have first:=ForwardCopyMemory.copied_bytes (wrappedMemory p q) (scratch p+60).toNat (scratch p+108).toNat 36 wrapped.1 (first_copy_bounds p q hn hd).1
      (Or.inl (by rw[a60,a108];omega)) (i-4) (by omega)
    rw[scratchMemory,first]
    have eq:(scratch p+108).toNat+(i-4)=(scratch p).toNat+104+i:=by rw[a108];omega
    exact congrArg (fun address:Nat=>(wrappedMemory p q).read8 address) eq

theorem final_record_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hout:p.sp161.toNat≤p.out161.toNat)(i:Nat)(hi:i<40):
    (finalMemory p q).read8 (p.out161.toNat+8+i)=
      (wrappedMemory p q).read8 ((scratch p).toNat+104+i):=by
  have n:=scratch_numbers p hn
  have a16:(scratch p+16).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have o8:(p.out161+8).toNat=p.out161.toNat+8:=by
    have b:=hn.outBound;have w:=hn.width
    rw[UInt32.toNat_add];simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have shape:=acceptedMemory_spec p q hn hd
  have result:=resultMemory_spec p q hn hd
  have b:=hn.outBound
  have tag:=writeI32_spec (resultMemory p q) p.out161.toNat 0 result.1 (by rw[result.2.1];omega)
  rw[finalMemory,tag.2.2.2,ite_eq_right (by omega)]
  have copied:=ForwardCopyMemory.copied_bytes (acceptedMemory p q) (p.out161+8).toNat (scratch p+16).toNat 40 shape.1 (result_copy_bounds p q hn hd).1
    (Or.inr (by rw[o8,a16];omega)) i hi
  rw[o8] at copied
  rw[resultMemory,o8,copied,a16]
  exact accepted_record_bytes p q hn hd i hi

private theorem read32_eq(m n:Memory)(a b:Nat)(h:∀i,i<4→m.read8 (a+i)=n.read8 (b+i)):
    readI32 m a=readI32 n b:=by
  have zero:=h 0 (by omega)
  simp only[Nat.add_zero] at zero
  simp[readI32,List.range_succ,h,zero]

theorem final_record_words(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hout:p.sp161.toNat≤p.out161.toNat):
    (∀offset,offset=8∨offset=16∨offset=24∨offset=32→
      readI64 (finalMemory p q) (p.out161.toNat+offset)=readI64 (wrappedMemory p q) ((scratch p).toNat+96+offset)) ∧
    (∀offset,offset=32∨offset=36∨offset=40∨offset=44→
      readI32 (finalMemory p q) (p.out161.toNat+offset)=readI32 (wrappedMemory p q) ((scratch p).toNat+96+offset)):=by
  constructor
  · intro offset ho
    apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw[AllocateLayoutWrapperReadback.readI64_byte _ _ i hi]
    have bytes:=final_record_bytes p q hn hd hout (offset-8+i) (by rcases ho with rfl|rfl|rfl|rfl <;> omega)
    have a:p.out161.toNat+8+(offset-8+i)=p.out161.toNat+offset+i:=by rcases ho with rfl|rfl|rfl|rfl <;> omega
    have b:(scratch p).toNat+104+(offset-8+i)=(scratch p).toNat+96+offset+i:=by rcases ho with rfl|rfl|rfl|rfl <;> omega
    rw[a,b] at bytes;exact bytes
  · intro offset ho
    apply read32_eq
    intro i hi
    have bytes:=final_record_bytes p q hn hd hout (offset-8+i) (by rcases ho with rfl|rfl|rfl|rfl <;> omega)
    have a:p.out161.toNat+8+(offset-8+i)=p.out161.toNat+offset+i:=by rcases ho with rfl|rfl|rfl|rfl <;> omega
    have b:(scratch p).toNat+104+(offset-8+i)=(scratch p).toNat+96+offset+i:=by rcases ho with rfl|rfl|rfl|rfl <;> omega
    rw[a,b] at bytes;exact bytes

theorem finalMemory_tag(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    readI32 (finalMemory p q) p.out161.toNat=0:=by
  have shape:=resultMemory_spec p q hn hd
  have b:=hn.outBound
  unfold finalMemory
  exact PanicAllocateReadback.read_write_self (resultMemory p q) p.out161.toNat 0 shape.1 (by rw[shape.2.1];omega)
end WNear.Proofs.StateDecodeBorshRead
