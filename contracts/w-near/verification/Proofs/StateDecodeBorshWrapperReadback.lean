import Proofs.StateDecodeBorshWrapperNative
import Proofs.AllocateLayoutWrapperReadback

/-! Canonical162 record bytes. The operational contract permits arbitrary
output aliases; this readback explicitly requires original output above SP. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
attribute [local irreducible] decodedMemory firstMemory packedMemory secondMemory finalMemory packedValue

private theorem shifted_byte(value:UInt64)(i:Nat)(hi:i<4):
    UInt8.ofNat ((UInt32.ofNat ((value >>>32).toNat)).toNat >>>(8*i))=
      UInt8.ofNat (value.toNat >>>(8*(4+i))):=by
  apply UInt8.toNat_inj.mp
  have cases:i=0 ∨i=1 ∨i=2 ∨i=3:=by omega
  rcases cases with rfl|rfl|rfl|rfl <;> simp[UInt64.toNat_shiftRight,Nat.shiftRight_eq_div_pow] <;> omega

/-- The cached upper32 bits retain the four original bytes after the status. -/
theorem packedValue_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(i:Nat)(hi:i<4):
    UInt8.ofNat ((UInt32.ofNat ((packedValue p q >>>32).toNat)).toNat >>>(8*i))=
      (decodedMemory p q).read8 ((scratch p).toNat+56+i):=by
  rw[shifted_byte _ i hi,packedValue,AllocateLayoutWrapperReadback.readI64_byte _ _ (4+i) (by omega)]
  congr 1
  omega

/-- The two disjoint scratch/output copies and cached word reconstruct all
40 bytes following the original425 status/padding: fields and trailing padding. -/
theorem final_record_bytes(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hout:p.sp162.toNat≤p.out162.toNat)
    (i:Nat)(hi:i<40):
    (finalMemory p q).read8 (p.out162.toNat+8+i)=
      (decodedMemory p q).read8 ((scratch p).toNat+56+i):=by
  have sn:=scratch_numbers p hn
  have shapeD:=decodedMemory_spec p q hn hd
  have shapeF:=firstMemory_spec p q hn hd
  have shapeP:=packedMemory_spec p q hn hd
  have shapeS:=secondMemory_spec p q hn hd
  have a12:(scratch p+12).toNat=(scratch p).toNat+12:=scratch_add p hn 12 (by omega)
  have a60:((scratch p+48)+12).toNat=(scratch p).toNat+60:=by rw[UInt32.add_assoc];exact scratch_add p hn 60 (by omega)
  have o8:(p.out162+8).toNat=p.out162.toNat+8:=output_add p hn 8 (by omega)
  have o12:(p.out162+12).toNat=p.out162.toNat+12:=output_add p hn 12 (by omega)
  have bounds:=hn.outputBound
  have tag:=writeI32_spec (secondMemory p q) p.out162.toNat 0 shapeS.1 (by rw[shapeS.2.1];omega)
  rw[finalMemory,tag.2.2.2,ite_eq_right (by omega)]
  have packed:=writeI32_spec (firstMemory p q) (p.out162+8).toNat (UInt32.ofNat ((packedValue p q >>>32).toNat)) shapeF.1 (by rw[o8,shapeF.2.1];omega)
  by_cases low:i<4
  · have copied:=ForwardCopyMemory.spec (packedMemory p q) (p.out162+12).toNat (scratch p+12).toNat 36 shapeP.1 (second_copy_bounds p q hn hd).1
    rw[secondMemory,copied.2.2.2 _ (Or.inl (by omega)),packedMemory,packed.2.2.2,ite_eq_left (by omega)]
    have idx:p.out162.toNat+8+i-(p.out162+8).toNat=i:=by omega
    rw[idx]
    exact packedValue_bytes p q i low
  · have second:=ForwardCopyMemory.copied_bytes (packedMemory p q) (p.out162+12).toNat (scratch p+12).toNat 36 shapeP.1 (second_copy_bounds p q hn hd).1 (Or.inr (by omega)) (i-4) (by omega)
    have dest:(p.out162+12).toNat+(i-4)=p.out162.toNat+8+i:=by omega
    rw[dest] at second
    rw[secondMemory,second]
    rw[packedMemory,packed.2.2.2,ite_eq_right (by omega)]
    have first:=ForwardCopyMemory.copied_bytes (decodedMemory p q) (scratch p+12).toNat ((scratch p+48)+12).toNat 36 shapeD.1 (first_copy_bounds p q hn hd).1 (Or.inl (by omega)) (i-4) (by omega)
    rw[firstMemory,first]
    have source:((scratch p+48)+12).toNat+(i-4)=(scratch p).toNat+56+i:=by omega
    rw[source]

/-- All actual162 output words refer to the corresponding original425 fields. -/
theorem final_record_words(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hout:p.sp162.toNat≤p.out162.toNat):
    (∀ offset,offset=8 ∨offset=16 ∨offset=24 ∨offset=32 →
      readI64 (finalMemory p q) (p.out162.toNat+offset)=
        readI64 (decodedMemory p q) ((scratch p).toNat+48+offset)) ∧
    (∀ offset,offset=40 ∨offset=44 →
      readI32 (finalMemory p q) (p.out162.toNat+offset)=
        readI32 (decodedMemory p q) ((scratch p).toNat+48+offset)):=by
  constructor
  · intro offset ho
    apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw[AllocateLayoutWrapperReadback.readI64_byte _ _ i hi]
    have b:=final_record_bytes p q hn hd hout (offset-8+i) (by rcases ho with rfl|rfl|rfl|rfl <;> omega)
    have o:8+(offset-8+i)=offset+i:=by rcases ho with rfl|rfl|rfl|rfl <;> omega
    have a:(scratch p).toNat+56+(offset-8+i)=(scratch p).toNat+48+offset+i:=by rcases ho with rfl|rfl|rfl|rfl <;> omega
    have z:p.out162.toNat+8+(offset-8+i)=p.out162.toNat+offset+i:=by omega
    rw[z,a] at b
    exact b
  · intro offset ho
    have bytes(i:Nat)(hi:i<4):
        (finalMemory p q).read8 (p.out162.toNat+offset+i)=
        (decodedMemory p q).read8 ((scratch p).toNat+48+offset+i):=by
      have b:=final_record_bytes p q hn hd hout (offset-8+i) (by rcases ho with rfl|rfl <;> omega)
      have a:p.out162.toNat+8+(offset-8+i)=p.out162.toNat+offset+i:=by rcases ho with rfl|rfl <;> omega
      have z:(scratch p).toNat+56+(offset-8+i)=(scratch p).toNat+48+offset+i:=by rcases ho with rfl|rfl <;> omega
      simpa only[a,z] using b
    have zero:(finalMemory p q).read8 (p.out162.toNat+offset)=
        (decodedMemory p q).read8 ((scratch p).toNat+48+offset):=by simpa only[Nat.add_zero] using bytes 0 (by omega)
    simp[readI32,List.range_succ,bytes,zero]

/-- The final status store is last and is unconditionally zero on this path. -/
theorem finalMemory_tag(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    readI32 (finalMemory p q) p.out162.toNat=0:=by
  have shape:=secondMemory_spec p q hn hd
  have bound:=hn.outputBound
  have store:=writeI32_spec (secondMemory p q) p.out162.toNat 0 shape.1 (by rw[shape.2.1];omega)
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  rw[finalMemory,store.2.2.2,ite_eq_left (by omega),Nat.add_sub_cancel_left]
end WNear.Proofs.StateDecodeBorshWrapper
