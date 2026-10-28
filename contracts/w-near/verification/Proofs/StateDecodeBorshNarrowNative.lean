import Proofs.StateDecodeBorshWideNative
import Proofs.StateDecodeScalarSliceOutput

/-! The second scalar reader's original domain, reconstructed through actual372
and all three deployed save writes. No future scalar domain is assumed. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem savedWideMemory_specs (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    (wideFirstMemory p q).wf ∧(wideFirstMemory p q).byteSize=p.memory.byteSize ∧
    (wideSecondMemory p q).wf ∧(wideSecondMemory p q).byteSize=p.memory.byteSize ∧
    (savedWideMemory p q).wf ∧(savedWideMemory p q).byteSize=p.memory.byteSize ∧
    (savedWideMemory p q).max=p.memory.max := by
  have wn:=wide_native p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) wn
  have prev:=savedPrefixMemory_spec p q hn hd
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at shape
  have n:=scratch_numbers p hn
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=by
    have eq:(scratch p+32)+8=scratch p+40:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 40 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have first:=writeI64_spec (wideMemory p q) ((scratch p+32)+8).toNat (readI64 (wideMemory p q) (scratch p+68).toNat) shape.1 (by rw[a40,shape.2.1,prev.2.1];omega)
  have second:=writeI32_spec (wideFirstMemory p q) (scratch p+48).toNat (readI32 (wideFirstMemory p q) (scratch p+76).toNat) first.1 (by unfold wideFirstMemory;rw[a48,first.2.1,shape.2.1,prev.2.1];omega)
  have third:=writeI64_spec (wideSecondMemory p q) ((scratch p).toNat+32) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60)) second.1 (by unfold wideSecondMemory;rw[second.2.1];unfold wideFirstMemory;rw[first.2.1,shape.2.1,prev.2.1];omega)
  exact ⟨first.1,first.2.1.trans (shape.2.1.trans prev.2.1),second.1,second.2.1.trans (first.2.1.trans (shape.2.1.trans prev.2.1)),third.1,third.2.1.trans (second.2.1.trans (first.2.1.trans (shape.2.1.trans prev.2.1))),third.2.2.1.trans (second.2.2.1.trans (first.2.2.1.trans (shape.2.2.trans prev.2.2)))⟩

theorem savedWide_descriptor (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    readI32 (savedWideMemory p q) p.slice.toNat=narrowPointer p ∧
    readI32 (savedWideMemory p q) (p.slice.toNat+4)=narrowLength p := by
  have wn:=wide_native p q hn hd
  have prev:=savedPrefixMemory_spec p q hn hd
  have words:=savedPrefix_descriptor p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) wn
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at shape
  have n:=scratch_numbers p hn
  have above:=hn.descriptorAbove
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have record:=StateDecodeScalar.finalMemory_slice_words true (wideLayout p q) wn (Or.inl (by change (scratch p+56).toNat+4≤p.slice.toNat;rw[a56];omega))
  change readI32 (wideMemory p q) p.slice.toNat=readI32 (savedPrefixMemory p q) p.slice.toNat+16 ∧readI32 (wideMemory p q) (p.slice.toNat+4)=readI32 (savedPrefixMemory p q) (p.slice.toNat+4)-16 at record
  rw[words.1,words.2] at record
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=by
    have eq:(scratch p+32)+8=scratch p+40:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 40 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have first:=writeI64_spec (wideMemory p q) ((scratch p+32)+8).toNat (readI64 (wideMemory p q) (scratch p+68).toNat) shape.1 (by rw[a40,shape.2.1,prev.2.1];omega)
  have second:=writeI32_spec (wideFirstMemory p q) (scratch p+48).toNat (readI32 (wideFirstMemory p q) (scratch p+76).toNat) first.1 (by unfold wideFirstMemory;rw[a48,first.2.1,shape.2.1,prev.2.1];omega)
  have third:=writeI64_spec (wideSecondMemory p q) ((scratch p).toNat+32) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60)) second.1 (by unfold wideSecondMemory;rw[second.2.1];unfold wideFirstMemory;rw[first.2.1,shape.2.1,prev.2.1];omega)
  have frame(address : Nat)(ha:p.slice.toNat≤address):readI32 (savedWideMemory p q) address=readI32 (wideMemory p q) address:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold savedWideMemory
    rw[third.2.2.2,ite_eq_right (show ¬((scratch p).toNat+32≤address+i ∧address+i<(scratch p).toNat+32+8) from by omega)]
    unfold wideSecondMemory
    rw[second.2.2.2,ite_eq_right (show ¬((scratch p+48).toNat≤address+i ∧address+i<(scratch p+48).toNat+4) from by rw[a48];omega)]
    unfold wideFirstMemory
    rw[first.2.2.2]
    exact ite_eq_right (by rw[a40];omega)
  exact ⟨(frame _ (by omega)).trans record.1,(frame _ (by omega)).trans record.2⟩

theorem narrow_native (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) : StateDecodeScalar.Native false (narrowLayout p q) := by
  have shapes:=savedWideMemory_specs p q hn hd
  have shape:=shapes.2.2.2.2
  have words:=savedWide_descriptor p q hn hd
  have nums:=narrow_numbers p hn
  have sn:=scratch_numbers p hn
  have out:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have lower:=hn.spLower
  have desc:=hn.descriptorAbove
  have db:=hn.prefixNative.child.sliceBound
  have width:=hn.prefixNative.child.memoryWidth
  refine ⟨shape.1,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,?_,?_,?_⟩
  · change (savedWideMemory p q).byteSize≤2^32;rw[shape.2.1];exact width
  · change 48≤(scratch p).toNat;omega
  · change (scratch p).toNat≤(savedWideMemory p q).byteSize;rw[shape.2.1];omega
  · change (scratch p).toNat≤(scratch p+56).toNat;rw[out];omega
  · change (scratch p+56).toNat+16≤(savedWideMemory p q).byteSize;rw[out,shape.2.1];omega
  · change (scratch p).toNat≤p.slice.toNat;omega
  · change p.slice.toNat+8≤(savedWideMemory p q).byteSize;rw[shape.2.1];exact db
  · change 8≤(readI32 (savedWideMemory p q) (p.slice.toNat+4)).toNat;rw[words.2];omega
  · change (scratch p).toNat≤(readI32 (savedWideMemory p q) p.slice.toNat).toNat;rw[words.1];omega
  · change (readI32 (savedWideMemory p q) p.slice.toNat).toNat+8≤(savedWideMemory p q).byteSize;rw[words.1,shape.2.1];omega
end WNear.Proofs.StateDecodeBorsh
