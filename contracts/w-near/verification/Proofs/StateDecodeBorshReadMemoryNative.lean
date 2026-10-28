import Proofs.StateDecodeBorshReadPhases
import Proofs.StateDecodeBorshReadDomain
import Proofs.StateDecodeBorshWrapperReadback

/-! Original161 native bounds justify each literal forward copy and the accepted
status. Memory effects retain arbitrary destination/source aliases. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem scratch_or4(p:Layout)(hn:Native p):
    ((scratch p+16)|||4).toNat=(scratch p).toNat+20:=by
  have n:=scratch_numbers p hn
  have aligned:=hn.spAligned
  have ha:(scratch p).toNat%16=0:=by omega
  have next:(scratch p+16).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  rw[UInt32.toNat_or,next]
  simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  have rem:((scratch p).toNat+16)%16=0:=by omega
  have div:=Nat.or_div_two_pow (a:=(scratch p).toNat+16) (b:=4) (n:=4)
  have mod:=Nat.or_mod_two_pow (a:=(scratch p).toNat+16) (b:=4) (n:=4)
  simp only[Nat.reducePow,Nat.reduceDiv,Nat.or_zero] at div
  simp only[Nat.reducePow,rem,Nat.reduceMod,Nat.zero_or] at mod
  have a:=Nat.mod_add_div (((scratch p).toNat+16)|||4) 16
  have b:=Nat.mod_add_div ((scratch p).toNat+16) 16
  omega

theorem wrappedMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (wrappedMemory p q).wf ∧(wrappedMemory p q).byteSize=p.memory.byteSize ∧(wrappedMemory p q).max=p.memory.max:=by
  have actual:=StateDecodeBorshWrapper.finalMemory_spec (actualWrapper p) (actualAllocation p q) (wrapper_native p hn) (accepted_domain p q hn hd)
  have shape:=setupMemory_spec p hn
  exact ⟨actual.1,actual.2.1.trans shape.2.1,actual.2.2.trans shape.2.2⟩

theorem tagValue_zero(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):tagValue p q=0:=by
  have tag:=StateDecodeBorshWrapper.finalMemory_tag (actualWrapper p) (actualAllocation p q) (wrapper_native p hn) (accepted_domain p q hn hd)
  have a96:(scratch p+96).toNat=(scratch p).toNat+96:=scratch_add p hn 96 (by omega)
  change readI32 (wrappedMemory p q) p.out162.toNat=0 at tag
  rw[hn.wrapperOut,a96] at tag
  exact tag

theorem first_copy_bounds(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (scratch p+60).toNat+36≤(wrappedMemory p q).byteSize ∧
    (scratch p+108).toNat+36≤(wrappedMemory p q).byteSize:=by
  have shape:=wrappedMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a60:(scratch p+60).toNat=(scratch p).toNat+60:=scratch_add p hn 60 (by omega)
  have a108:(scratch p+108).toNat=(scratch p).toNat+108:=scratch_add p hn 108 (by omega)
  rw[a60,a108,shape.2.1];omega

theorem scratchMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (scratchMemory p q).wf ∧(scratchMemory p q).byteSize=p.memory.byteSize ∧(scratchMemory p q).max=p.memory.max:=by
  have shape:=wrappedMemory_spec p q hn hd
  have copy:=ForwardCopyMemory.spec (wrappedMemory p q) (scratch p+60).toNat (scratch p+108).toNat 36 shape.1 (first_copy_bounds p q hn hd).1
  exact ⟨copy.1,copy.2.1.trans shape.2.1,copy.2.2.1.trans shape.2.2⟩

theorem upperMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (upperMemory p q).wf ∧(upperMemory p q).byteSize=p.memory.byteSize ∧(upperMemory p q).max=p.memory.max:=by
  have shape:=scratchMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have store:=writeI32_spec (scratchMemory p q) ((scratch p).toNat+16) (UInt32.ofNat ((packedValue p q>>>32).toNat)) shape.1 (by rw[shape.2.1];omega)
  exact ⟨store.1,store.2.1.trans shape.2.1,store.2.2.1.trans shape.2.2⟩

theorem accepted_copy_bounds(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    ((scratch p+16)|||4).toNat+36≤(upperMemory p q).byteSize ∧
    (scratch p+60).toNat+36≤(upperMemory p q).byteSize:=by
  have shape:=upperMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a60:(scratch p+60).toNat=(scratch p).toNat+60:=scratch_add p hn 60 (by omega)
  rw[scratch_or4 p hn,a60,shape.2.1];omega

theorem acceptedMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (acceptedMemory p q).wf ∧(acceptedMemory p q).byteSize=p.memory.byteSize ∧(acceptedMemory p q).max=p.memory.max:=by
  have shape:=upperMemory_spec p q hn hd
  have copy:=ForwardCopyMemory.spec (upperMemory p q) ((scratch p+16)|||4).toNat (scratch p+60).toNat 36 shape.1 (accepted_copy_bounds p q hn hd).1
  exact ⟨copy.1,copy.2.1.trans shape.2.1,copy.2.2.1.trans shape.2.2⟩

theorem result_copy_bounds(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (p.out161+8).toNat+40≤(acceptedMemory p q).byteSize ∧
    (scratch p+16).toNat+40≤(acceptedMemory p q).byteSize:=by
  have shape:=acceptedMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a16:(scratch p+16).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have out:(p.out161+8).toNat=p.out161.toNat+8:=by
    have hb:=hn.outBound
    have hw:=hn.width
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have hb:=hn.outBound
  rw[out,a16,shape.2.1];omega

theorem resultMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (resultMemory p q).wf ∧(resultMemory p q).byteSize=p.memory.byteSize ∧(resultMemory p q).max=p.memory.max:=by
  have shape:=acceptedMemory_spec p q hn hd
  have copy:=ForwardCopyMemory.spec (acceptedMemory p q) (p.out161+8).toNat (scratch p+16).toNat 40 shape.1 (result_copy_bounds p q hn hd).1
  exact ⟨copy.1,copy.2.1.trans shape.2.1,copy.2.2.1.trans shape.2.2⟩

theorem finalMemory_spec(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    (finalMemory p q).wf ∧(finalMemory p q).byteSize=p.memory.byteSize ∧(finalMemory p q).max=p.memory.max:=by
  have shape:=resultMemory_spec p q hn hd
  have hb:=hn.outBound
  have store:=writeI32_spec (resultMemory p q) p.out161.toNat 0 shape.1 (by rw[shape.2.1];omega)
  exact ⟨store.1,store.2.1.trans shape.2.1,store.2.2.1.trans shape.2.2⟩
end WNear.Proofs.StateDecodeBorshRead
