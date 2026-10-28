import Proofs.StateDecodePrefixNative
import Proofs.AllocateLayoutWrapperReadback

/-! Original prefix bytes survive all actual scratch outputs and the early
caller-slice advance, under the explicit original descriptor/payload separation. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI64

private theorem scratch_slice_spec (drop : Bool) (p : Layout) (hn:Native p) (m:Memory) (offset:Nat)
    (ptr len split:UInt32) (hw:m.wf) (size:m.byteSize=p.memory.byteSize) (hmax:m.max=p.memory.max)
    (ha:offset+8≤64) :
    let out:=scratch p+UInt32.ofNat offset
    let after:=StateDecodeSlices.finalMemory drop m out ptr len split
    after.wf ∧after.byteSize=p.memory.byteSize ∧after.max=p.memory.max ∧
    ∀j,p.sp.toNat≤j→after.read8 j=m.read8 j := by
  have add:=scratch_add p hn offset (by omega)
  have e:=scratch_end p hn
  have spb:=hn.spBound
  have bound:(scratch p+UInt32.ofNat offset).toNat+8≤m.byteSize:=by rw[add,size];omega
  have spec:=StateDecodeSlices.finalMemory_spec drop m (scratch p+UInt32.ofNat offset) ptr len split hw bound
  refine ⟨spec.1,spec.2.1.trans size,spec.2.2.1.trans hmax,?_⟩
  intro j hj
  rw[spec.2.2.2]
  have no1:¬((scratch p+UInt32.ofNat offset).toNat≤j ∧j<(scratch p+UInt32.ofNat offset).toNat+4):=by rw[add];omega
  have no2:¬((scratch p+UInt32.ofNat offset).toNat+4≤j ∧j<(scratch p+UInt32.ofNat offset).toNat+8):=by rw[add];omega
  simp only[ite_eq_right no1,ite_eq_right no2]

theorem takenFour_spec (p:Layout) (hn:Native p) :
    (takenFourMemory p).wf ∧(takenFourMemory p).byteSize=p.memory.byteSize ∧(takenFourMemory p).max=p.memory.max ∧
    ∀j,p.sp.toNat≤j→(takenFourMemory p).read8 j=p.memory.read8 j :=
  scratch_slice_spec false p hn p.memory 40 p.pointer p.length 4 hn.wf rfl rfl (by omega)

theorem droppedFour_spec (p:Layout) (hn:Native p) :
    (droppedFourMemory p).wf ∧(droppedFourMemory p).byteSize=p.memory.byteSize ∧(droppedFourMemory p).max=p.memory.max ∧
    ∀j,p.sp.toNat≤j→(droppedFourMemory p).read8 j=p.memory.read8 j := by
  have ht:=takenFour_spec p hn
  have hs:=scratch_slice_spec true p hn (takenFourMemory p) 32 p.pointer p.length 4 ht.1 ht.2.1 ht.2.2.1 (by omega)
  exact ⟨hs.1,hs.2.1,hs.2.2.1,fun j hj=>(hs.2.2.2 j hj).trans (ht.2.2.2 j hj)⟩

theorem advancedMemory_spec (p:Layout) (hn:Native p) :
    (advancedMemory p).wf ∧(advancedMemory p).byteSize=p.memory.byteSize ∧(advancedMemory p).max=p.memory.max ∧
    ∀j,p.pointer.toNat≤j→j<p.pointer.toNat+4+(count p).toNat→(advancedMemory p).read8 j=p.memory.read8 j := by
  have hd:=droppedFour_spec p hn
  have bound:p.slice.toNat+8≤(droppedFourMemory p).byteSize:=by rw[hd.2.1];exact hn.sliceBound
  have cp:=writeI64_spec (droppedFourMemory p) p.slice.toNat (advancedPacked p) hd.1 bound
  refine ⟨cp.1,cp.2.1.trans hd.2.1,cp.2.2.1.trans hd.2.2.1,?_⟩
  intro j hj hk
  unfold advancedMemory
  rw[cp.2.2.2]
  have no:¬(p.slice.toNat≤j ∧j<p.slice.toNat+8):=by rcases hn.slicePayloadSep with h|h <;> omega
  rw[ite_eq_right no]
  exact hd.2.2.2 _ (by have h:=hn.pointerAbove;omega)

theorem lengthMemory_spec (p:Layout) (hn:Native p) :
    (lengthMemory p).wf ∧(lengthMemory p).byteSize=p.memory.byteSize ∧(lengthMemory p).max=p.memory.max ∧
    ∀j,p.pointer.toNat≤j→j<p.pointer.toNat+4+(count p).toNat→(lengthMemory p).read8 j=p.memory.read8 j := by
  have ha:=advancedMemory_spec p hn
  have add:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have e:=scratch_end p hn
  have bound:(lengthOut p).toNat+8≤(advancedMemory p).byteSize:=by rw[add,ha.2.1];have h:=hn.spBound;omega
  have spec:=StateDecodePrefixLeaves.recordMemory_spec (advancedMemory p) (lengthOut p) (count p) ha.1 bound
  refine ⟨spec.1,spec.2.1.trans ha.2.1,spec.2.2.1.trans ha.2.2.1,?_⟩
  intro j hj hk
  unfold lengthMemory
  rw[spec.2.2.2]
  have hp:=hn.pointerAbove
  have no1:¬((lengthOut p).toNat≤j ∧j<(lengthOut p).toNat+4):=by rw[add];omega
  have no2:¬((lengthOut p).toNat+4≤j ∧j<(lengthOut p).toNat+8):=by rw[add];omega
  simp only[ite_eq_right no1,ite_eq_right no2]
  exact ha.2.2.2 j hj hk

theorem takenPayload_spec (p:Layout) (hn:Native p) :
    (takenPayloadMemory p).wf ∧(takenPayloadMemory p).byteSize=p.memory.byteSize ∧(takenPayloadMemory p).max=p.memory.max ∧
    ∀j,p.pointer.toNat≤j→j<p.pointer.toNat+4+(count p).toNat→(takenPayloadMemory p).read8 j=p.memory.read8 j := by
  have hl:=lengthMemory_spec p hn
  have hs:=scratch_slice_spec false p hn (lengthMemory p) 16 (payloadPointer p) (remaining p) (count p) hl.1 hl.2.1 hl.2.2.1 (by omega)
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_⟩
  intro j hj hk
  exact (hs.2.2.2 j (by have h:=hn.pointerAbove;omega)).trans (hl.2.2.2 j hj hk)
end WNear.Proofs.StateDecodePrefix
