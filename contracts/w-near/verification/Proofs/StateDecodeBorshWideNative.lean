import Proofs.StateDecodeBorshNative
import Proofs.StateDecodePrefixWrapperMemorySpec
import Proofs.StateDecodePrefixWrapperRecord

/-! The first scalar reader's domain follows from the original425 inputs and
actual315 descriptor writes, followed by the two deployed prefix saves. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem savedPrefixMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    (savedPrefixMemory p q).wf ∧(savedPrefixMemory p q).byteSize=p.memory.byteSize ∧
    (savedPrefixMemory p q).max=p.memory.max := by
  have shape:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  change (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize ∧(prefixMemory p q).max=p.memory.max at shape
  have n:=scratch_numbers p hn
  have h:=writeI32_spec (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) shape.1 (by rw[shape.2.1];omega)
  have l:=writeI64_spec (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q) h.1 (by unfold prefixHighMemory;rw[h.2.1,shape.2.1];omega)
  exact ⟨l.1,l.2.1.trans (h.2.1.trans shape.2.1),l.2.2.1.trans (h.2.2.1.trans shape.2.2)⟩

theorem savedPrefix_descriptor (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    readI32 (savedPrefixMemory p q) p.slice.toNat=widePointer p ∧
    readI32 (savedPrefixMemory p q) (p.slice.toNat+4)=wideLength p := by
  have n:=scratch_numbers p hn
  have above:=hn.descriptorAbove
  have child:=hn.prefixNative.childOut
  have childsp:=hn.prefixNative.childSP
  have ps:(StateDecodePrefixWrapper.scratch p.toPrefixWrapper).toNat=(scratch p).toNat-16:=by
    unfold StateDecodePrefixWrapper.scratch
    rw[hn.childSP,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have lo:=hn.spLower
    have lt:=(scratch p).toNat_lt
    omega
  have r:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have hc:p.out.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat:=by
    left
    rw[child,ps]
    have slo:=hn.spLower
    omega
  have ho:p.wrapperOut.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.wrapperOut.toNat:=by
    left;rw[hn.childOut,r];omega
  have record:=StateDecodePrefixWrapper.finalMemory_record p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain hc ho
  have shape:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  change (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize ∧(prefixMemory p q).max=p.memory.max at shape
  have hi:=writeI32_spec (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) shape.1 (by rw[shape.2.1];omega)
  have lo:=writeI64_spec (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q) hi.1 (by unfold prefixHighMemory;rw[hi.2.1,shape.2.1];omega)
  have frame (address : Nat) (ha:p.slice.toNat≤address) :
      readI32 (savedPrefixMemory p q) address=readI32 (prefixMemory p q) address:=by
    apply Allocate.readI32_congr_bytes
    intro i h
    unfold savedPrefixMemory
    rw[lo.2.2.2]
    have nl:¬((scratch p).toNat+16≤address+i ∧address+i<(scratch p).toNat+16+8):=by omega
    rw[ite_eq_right nl]
    unfold prefixHighMemory
    rw[hi.2.2.2]
    have nh:¬((scratch p).toNat+24≤address+i ∧address+i<(scratch p).toNat+24+4):=by omega
    exact ite_eq_right nh
  exact ⟨(frame _ (by omega)).trans record.2.2.2.2.1,(frame _ (by omega)).trans record.2.2.2.2.2⟩

theorem wide_native (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) : StateDecodeScalar.Native true (wideLayout p q) := by
  have shape:=savedPrefixMemory_spec p q hn hd
  have words:=savedPrefix_descriptor p q hn hd
  have nums:=header_numbers p hn
  have sn:=scratch_numbers p hn
  have out:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have lower:=hn.spLower
  have desc:=hn.descriptorAbove
  have db:=hn.prefixNative.child.sliceBound
  have width:=hn.prefixNative.child.memoryWidth
  refine ⟨shape.1,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,?_,?_,?_⟩
  · change (savedPrefixMemory p q).byteSize≤2^32;rw[shape.2.1];exact width
  · change 48≤(scratch p).toNat;omega
  · change (scratch p).toNat≤(savedPrefixMemory p q).byteSize;rw[shape.2.1];omega
  · change (scratch p).toNat≤(scratch p+56).toNat;rw[out];omega
  · change (scratch p+56).toNat+24≤(savedPrefixMemory p q).byteSize;rw[out,shape.2.1];omega
  · change (scratch p).toNat≤p.slice.toNat;omega
  · change p.slice.toNat+8≤(savedPrefixMemory p q).byteSize;rw[shape.2.1];exact db
  · change 16≤(readI32 (savedPrefixMemory p q) (p.slice.toNat+4)).toNat;rw[words.2];omega
  · change (scratch p).toNat≤(readI32 (savedPrefixMemory p q) p.slice.toNat).toNat;rw[words.1];omega
  · change (readI32 (savedPrefixMemory p q) p.slice.toNat).toNat+16≤(savedPrefixMemory p q).byteSize;rw[words.1,shape.2.1];omega
end WNear.Proofs.StateDecodeBorsh
