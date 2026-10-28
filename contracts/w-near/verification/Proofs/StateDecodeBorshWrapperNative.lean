import Proofs.StateDecodeBorshWrapperState
import Proofs.StateDecodeBorshOutputRecord

/-! Original162 geometry supplies both real36-byte copy bounds and its accepted
guard tag. The second copy retains arbitrary output/scratch overlap. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem scratch_numbers(p:Layout)(hn:Native p):
    (scratch p).toNat=p.sp162.toNat-96 ∧(scratch p).toNat+96=p.sp162.toNat ∧
    (scratch p).toNat+96≤p.memory.byteSize ∧scratch p+96=p.sp162:=by
  have lo:=hn.spLower
  have lt:=p.sp162.toNat_lt
  have eq:(scratch p).toNat=p.sp162.toNat-96:=by
    rw[scratch,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨eq,by omega,by have b:=hn.spBound;omega,UInt32.sub_add_cancel p.sp162 96⟩

theorem scratch_add(p:Layout)(hn:Native p)(offset:Nat)(ho:offset<96):
    (scratch p+UInt32.ofNat offset).toNat=(scratch p).toNat+offset:=by
  have n:=scratch_numbers p hn
  have lt:=p.sp162.toNat_lt
  have off:offset<2^32:=by omega
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off]
  exact Nat.mod_eq_of_lt (by omega)

theorem output_add(p:Layout)(hn:Native p)(offset:Nat)(ho:offset<48):
    (p.out162+UInt32.ofNat offset).toNat=p.out162.toNat+offset:=by
  have b:=hn.outputBound
  have w:=hn.child.prefixNative.child.memoryWidth
  have off:offset<2^32:=by omega
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off]
  exact Nat.mod_eq_of_lt (by omega)

theorem decodedMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (decodedMemory p q).wf ∧(decodedMemory p q).byteSize=p.memory.byteSize ∧(decodedMemory p q).max=p.memory.max:=
  StateDecodeBorsh.finalMemory_spec p.toBorsh q hn.child hd

theorem tagValue_zero(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):tagValue p q=0:=by
  have tag:=(StateDecodeBorsh.finalMemory_record p.toBorsh q hn.child hd).1
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  rw[hn.childOut,a48] at tag
  exact tag

theorem first_copy_bounds(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (scratch p+12).toNat+36≤(decodedMemory p q).byteSize ∧
    ((scratch p+48)+12).toNat+36≤(decodedMemory p q).byteSize:=by
  have shape:=decodedMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a12:(scratch p+12).toNat=(scratch p).toNat+12:=scratch_add p hn 12 (by omega)
  have a60:((scratch p+48)+12).toNat=(scratch p).toNat+60:=by rw[UInt32.add_assoc];exact scratch_add p hn 60 (by omega)
  rw[a12,a60,shape.2.1]
  omega

theorem firstMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (firstMemory p q).wf ∧(firstMemory p q).byteSize=p.memory.byteSize ∧(firstMemory p q).max=p.memory.max:=by
  have original:=decodedMemory_spec p q hn hd
  have copy:=ForwardCopyMemory.spec (decodedMemory p q) (scratch p+12).toNat ((scratch p+48)+12).toNat 36 original.1 (first_copy_bounds p q hn hd).1
  exact ⟨copy.1,copy.2.1.trans original.2.1,copy.2.2.1.trans original.2.2⟩

theorem packedMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (packedMemory p q).wf ∧(packedMemory p q).byteSize=p.memory.byteSize ∧(packedMemory p q).max=p.memory.max:=by
  have original:=firstMemory_spec p q hn hd
  have a8:(p.out162+8).toNat=p.out162.toNat+8:=output_add p hn 8 (by omega)
  have bound:=hn.outputBound
  have store:=writeI32_spec (firstMemory p q) (p.out162+8).toNat (UInt32.ofNat ((packedValue p q >>>32).toNat)) original.1 (by rw[a8,original.2.1];omega)
  exact ⟨store.1,store.2.1.trans original.2.1,store.2.2.1.trans original.2.2⟩

theorem second_copy_bounds(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (p.out162+12).toNat+36≤(packedMemory p q).byteSize ∧
    (scratch p+12).toNat+36≤(packedMemory p q).byteSize:=by
  have original:=packedMemory_spec p q hn hd
  have a12:(p.out162+12).toNat=p.out162.toNat+12:=output_add p hn 12 (by omega)
  have b12:(scratch p+12).toNat=(scratch p).toNat+12:=scratch_add p hn 12 (by omega)
  have bound:=hn.outputBound
  have n:=scratch_numbers p hn
  rw[a12,b12,original.2.1]
  omega

theorem secondMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (secondMemory p q).wf ∧(secondMemory p q).byteSize=p.memory.byteSize ∧(secondMemory p q).max=p.memory.max:=by
  have original:=packedMemory_spec p q hn hd
  have copy:=ForwardCopyMemory.spec (packedMemory p q) (p.out162+12).toNat (scratch p+12).toNat 36 original.1 (second_copy_bounds p q hn hd).1
  exact ⟨copy.1,copy.2.1.trans original.2.1,copy.2.2.1.trans original.2.2⟩

theorem finalMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)
    (hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q):
    (finalMemory p q).wf ∧(finalMemory p q).byteSize=p.memory.byteSize ∧(finalMemory p q).max=p.memory.max:=by
  have original:=secondMemory_spec p q hn hd
  have bound:=hn.outputBound
  have store:=writeI32_spec (secondMemory p q) p.out162.toNat 0 original.1 (by rw[original.2.1];omega)
  exact ⟨store.1,store.2.1.trans original.2.1,store.2.2.1.trans original.2.2⟩
end WNear.Proofs.StateDecodeBorshWrapper
