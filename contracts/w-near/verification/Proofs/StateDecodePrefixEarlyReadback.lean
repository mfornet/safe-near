import Proofs.StateDecodePrefixEarlyLocals

/-! Original slice words survive take-four; the length leaf preserves the
already advanced slice pointer. All readbacks follow original Native bounds. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI64

theorem taken_slice_low (p : Layout) (hn : Native p) :
    readI32 (takenFourMemory p) p.slice.toNat=p.pointer := by
  have spec:=takenFour_spec p hn
  have eq:readI32 (takenFourMemory p) p.slice.toNat=readI32 p.memory p.slice.toNat:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact spec.2.2.2 _ (by have h:=hn.sliceAbove;omega)
  exact eq.trans hn.pointerRead

theorem taken_slice_high (p : Layout) (hn : Native p) :
    readI32 (takenFourMemory p) (p.slice.toNat+4)=p.length := by
  have spec:=takenFour_spec p hn
  have eq:readI32 (takenFourMemory p) (p.slice.toNat+4)=readI32 p.memory (p.slice.toNat+4):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact spec.2.2.2 _ (by have h:=hn.sliceAbove;omega)
  exact eq.trans hn.lengthRead

theorem length_slice_low (p : Layout) (hn : Native p) :
    readI32 (lengthMemory p) p.slice.toNat=payloadPointer p := by
  have ha:=advancedMemory_spec p hn
  have add:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have hend:=scratch_end p hn
  have hb:(lengthOut p).toNat+8≤(advancedMemory p).byteSize:=by
    rw[add,ha.2.1];have h:=hn.spBound;omega
  have spec:=StateDecodePrefixLeaves.recordMemory_spec (advancedMemory p) (lengthOut p) (count p) ha.1 hb
  have eq:readI32 (lengthMemory p) p.slice.toNat=readI32 (advancedMemory p) p.slice.toNat:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold lengthMemory
    rw[spec.2.2.2]
    have hs:=hn.sliceAbove
    have no1:¬((lengthOut p).toNat≤p.slice.toNat+i ∧p.slice.toNat+i<(lengthOut p).toNat+4):=by rw[add];omega
    have no2:¬((lengthOut p).toNat+4≤p.slice.toNat+i ∧p.slice.toNat+i<(lengthOut p).toNat+8):=by rw[add];omega
    simp only[ite_eq_right no1,ite_eq_right no2]
  exact eq.trans (advanced_low p hn)
end WNear.Proofs.StateDecodePrefix
