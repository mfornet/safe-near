import Proofs.StateDecodePrefixReadback

/-! The early316 memory footprint is its below-SP scratch plus the original
slice descriptor. Allocation-domain transport can therefore use original heap
word separations, without assuming anything about a future execution. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI64

private theorem length_above_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : p.sp.toNat≤j) : (lengthMemory p).read8 j=(advancedMemory p).read8 j := by
  have ha:=advancedMemory_spec p hn
  have add:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have e:=scratch_end p hn
  have hb:(lengthOut p).toNat+8≤(advancedMemory p).byteSize:=by
    rw[add,ha.2.1];have h:=hn.spBound;omega
  have spec:=StateDecodePrefixLeaves.recordMemory_spec (advancedMemory p) (lengthOut p) (count p) ha.1 hb
  have no1:¬((lengthOut p).toNat≤j ∧j<(lengthOut p).toNat+4):=by rw[add];omega
  have no2:¬((lengthOut p).toNat+4≤j ∧j<(lengthOut p).toNat+8):=by rw[add];omega
  unfold lengthMemory
  rw[spec.2.2.2]
  simp only[ite_eq_right no1,ite_eq_right no2]

theorem takenPayload_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : p.sp.toNat≤j) (hsep : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (takenPayloadMemory p).read8 j=p.memory.read8 j := by
  have hl:=lengthMemory_spec p hn
  have add:(takePayloadOut p).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have e:=scratch_end p hn
  have hb:(takePayloadOut p).toNat+8≤(lengthMemory p).byteSize:=by
    rw[add,hl.2.1];have h:=hn.spBound;omega
  have spec:=StateDecodeSlices.finalMemory_spec false (lengthMemory p) (takePayloadOut p)
    (payloadPointer p) (remaining p) (count p) hl.1 hb
  have no1:¬((takePayloadOut p).toNat≤j ∧j<(takePayloadOut p).toNat+4):=by rw[add];omega
  have no2:¬((takePayloadOut p).toNat+4≤j ∧j<(takePayloadOut p).toNat+8):=by rw[add];omega
  have frame:(takenPayloadMemory p).read8 j=(lengthMemory p).read8 j:=by
    unfold takenPayloadMemory
    rw[spec.2.2.2]
    simp only[ite_eq_right no1,ite_eq_right no2]
  have hd:=droppedFour_spec p hn
  have bound:p.slice.toNat+8≤(droppedFourMemory p).byteSize:=by rw[hd.2.1];exact hn.sliceBound
  have advance:=writeI64_spec (droppedFourMemory p) p.slice.toNat (advancedPacked p) hd.1 bound
  have no:¬(p.slice.toNat≤j ∧j<p.slice.toNat+8):=by omega
  have af:(advancedMemory p).read8 j=(droppedFourMemory p).read8 j:=by
    unfold advancedMemory
    rw[advance.2.2.2]
    exact ite_eq_right no
  exact frame.trans ((length_above_frame p hn j hj).trans (af.trans (hd.2.2.2 j hj)))

theorem takenPayload_word_frame (p : Layout) (hn : Native p) (address : Nat)
    (hj : p.sp.toNat≤address)
    (hsep : address+4≤p.slice.toNat ∨p.slice.toNat+8≤address) :
    readI32 (takenPayloadMemory p) address=readI32 p.memory address := by
  apply Allocate.readI32_congr_bytes
  intro i hi
  apply takenPayload_byte_frame p hn
  · omega
  · rcases hsep with h|h <;> omega
end WNear.Proofs.StateDecodePrefix
