import Proofs.StateDecodeBorshMemoryNative
import Proofs.StateDecodePrefixWrapperSourceFrame

/-! Original remaining Borsh header bytes survive prior decoder stages under
original heap/source separation. No future byte or execution facts are premises. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
private theorem write64_byte_frame (memory : Memory) (address : Nat) (value : UInt64) (j : Nat)
    (hw : memory.wf) (hb : address+8≤memory.byteSize) (hsep : j<address ∨address+8≤j) :
    (writeI64 memory address value).read8 j=memory.read8 j := by
  have spec:=writeI64_spec memory address value hw hb
  rw[spec.2.2.2]
  have no:¬(address≤j ∧j<address+8):=by omega
  exact ite_eq_right no

theorem finalMemory_byte_frame (wide : Bool) (p : Layout) (hn : Native wide p) (j : Nat)
    (hstack : p.sp.toNat≤j)
    (hout : j<p.out.toNat ∨p.out.toNat+(if wide then 24 else 16)≤j)
    (hslice : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (finalMemory wide p).read8 j=p.memory.read8 j := by
  have dropped:=droppedMemory_spec wide p hn
  have values:=valuesMemory_spec wide p hn
  have updated:=updatedMemory_spec wide p hn
  have addresses:=output_addresses wide p hn
  have ob:=hn.outBound
  have vf:(valuesMemory wide p).read8 j=(droppedMemory wide p).read8 j:=by
    cases wide with
    |false=>
      have lb:(p.out+8).toNat+8≤(droppedMemory false p).byteSize:=by rw[addresses.1,dropped.2.1];simp only[Bool.false_eq_true,ite_false] at ob;omega
      have sep:j<(p.out+8).toNat ∨(p.out+8).toNat+8≤j:=by rw[addresses.1];simp only[Bool.false_eq_true,ite_false] at hout;omega
      simpa only[valuesMemory,Bool.false_eq_true,ite_false] using write64_byte_frame _ _ _ j dropped.1 lb sep
    |true=>
      have hb:(p.out+16).toNat+8≤(droppedMemory true p).byteSize:=by rw[addresses.2 rfl,dropped.2.1];simp only[ite_true] at ob;omega
      have high:=writeI64_spec (droppedMemory true p) (p.out+16).toNat (highValue p) dropped.1 hb
      have lb:(p.out+8).toNat+8≤(writeI64 (droppedMemory true p) (p.out+16).toNat (highValue p)).byteSize:=by rw[high.2.1,addresses.1,dropped.2.1];simp only[ite_true] at ob;omega
      have hf:=write64_byte_frame (droppedMemory true p) (p.out+16).toNat (highValue p) j dropped.1 hb
        (by rw[addresses.2 rfl];simp only[ite_true] at hout;omega)
      have lf:=write64_byte_frame _ (p.out+8).toNat (lowValue true p) j high.1 lb
        (by rw[addresses.1];simp only[ite_true] at hout;omega)
      simpa only[valuesMemory,ite_true] using lf.trans hf
  have db:p.slice.toNat+8≤(valuesMemory wide p).byteSize:=by rw[values.2.1];exact hn.sliceBound
  have df:=write64_byte_frame (valuesMemory wide p) p.slice.toNat (dropValue wide p) j values.1 db hslice
  have tb:p.out.toNat+4≤(updatedMemory wide p).byteSize:=by rw[updated.2.1];cases wide <;> simp only[ite_true,Bool.false_eq_true,ite_false] at ob <;> omega
  have tag:=writeI32_spec (updatedMemory wide p) p.out.toNat 0 updated.1 tb
  have no:¬(p.out.toNat≤j ∧j<p.out.toNat+4):=by cases wide <;> simp only[ite_true,Bool.false_eq_true,ite_false] at hout <;> omega
  have tf:(finalMemory wide p).read8 j=(updatedMemory wide p).read8 j:=by unfold finalMemory;rw[tag.2.2.2];exact ite_eq_right no
  exact tf.trans (df.trans (vf.trans (dropped.2.2.2 j hstack)))
end WNear.Proofs.StateDecodeScalar

namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem write32_end (memory : Memory) (address : Nat) (value : UInt32) (j : Nat)
    (hw : memory.wf) (hb : address+4≤memory.byteSize) (he : address+4≤j) :
    (writeI32 memory address value).read8 j=memory.read8 j := by
  have spec:=writeI32_spec memory address value hw hb
  rw[spec.2.2.2]
  exact ite_eq_right (by omega)
private theorem write64_end (memory : Memory) (address : Nat) (value : UInt64) (j : Nat)
    (hw : memory.wf) (hb : address+8≤memory.byteSize) (he : address+8≤j) :
    (writeI64 memory address value).read8 j=memory.read8 j := by
  have spec:=writeI64_spec memory address value hw hb
  rw[spec.2.2.2]
  exact ite_eq_right (by omega)

private theorem header_geometry (p : Layout) (hn : Native p) (j : Nat)
    (hlo : (widePointer p).toNat≤j) (hhi : j<(widePointer p).toNat+24) :
    p.sp425.toNat≤j ∧(j<p.slice.toNat ∨p.slice.toNat+8≤j) := by
  have nums:=header_numbers p hn
  refine ⟨by omega,?_⟩
  rcases hn.descriptorHeaderSep with h|h
  · right;omega
  · left;omega

theorem prefixMemory_source_byte (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (j : Nat) (hlo : (widePointer p).toNat≤j) (hhi : j<(widePointer p).toNat+24) :
    (prefixMemory p q).read8 j=p.memory.read8 j := by
  have n:=scratch_numbers p hn
  have geo:=header_geometry p hn j hlo hhi
  have lower:=hn.spLower
  have sp:p.wrapperSP.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.childSP
  have out:p.wrapperOut.toNat=(scratch p).toNat+56:=by rw[hn.childOut];exact scratch_add p hn 56 (by omega)
  apply StateDecodePrefixWrapper.finalMemory_source_frame_above_sp p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain j
  · rw[sp];omega
  · rw[sp];omega
  · omega
  · rcases hroot with h|h <;> omega
  · right;rw[out];omega
  · exact geo.2

theorem savedPrefixMemory_source_byte (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (j : Nat) (hlo : (widePointer p).toNat≤j) (hhi : j<(widePointer p).toNat+24) :
    (savedPrefixMemory p q).read8 j=p.memory.read8 j := by
  have n:=scratch_numbers p hn
  have geo:=header_geometry p hn j hlo hhi
  have shape:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  change (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize ∧(prefixMemory p q).max=p.memory.max at shape
  have hb:(scratch p).toNat+24+4≤(prefixMemory p q).byteSize:=by rw[shape.2.1];omega
  have high:=writeI32_spec (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) shape.1 hb
  have lb:(scratch p).toNat+16+8≤(prefixHighMemory p q).byteSize:=by unfold prefixHighMemory;rw[high.2.1,shape.2.1];omega
  have hf:=write32_end (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) j shape.1 hb (by omega)
  have lf:=write64_end (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q) j high.1 lb (by omega)
  exact lf.trans (hf.trans (prefixMemory_source_byte p q hn hd hheap hroot j hlo hhi))

theorem savedWideMemory_source_byte (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (j : Nat) (hlo : (widePointer p).toNat≤j) (hhi : j<(widePointer p).toNat+24) :
    (savedWideMemory p q).read8 j=p.memory.read8 j := by
  have n:=scratch_numbers p hn
  have geo:=header_geometry p hn j hlo hhi
  have wn:=wide_native p q hn hd
  have prev:=savedPrefixMemory_spec p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) wn
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at shape
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have wf:(wideMemory p q).read8 j=(savedPrefixMemory p q).read8 j:=by
    apply StateDecodeScalar.finalMemory_byte_frame true (wideLayout p q) wn j
    · change (scratch p).toNat≤j;omega
    · change j<(scratch p+56).toNat ∨(scratch p+56).toNat+24≤j
      right;rw[a56];omega
    · exact geo.2
  have shapes:=savedWideMemory_specs p q hn hd
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=by
    have eq:(scratch p+32)+8=scratch p+40:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 40 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have fb:((scratch p+32)+8).toNat+8≤(wideMemory p q).byteSize:=by rw[a40,shape.2.1,prev.2.1];omega
  have sb:(scratch p+48).toNat+4≤(wideFirstMemory p q).byteSize:=by rw[a48,shapes.2.1];omega
  have tb:(scratch p).toNat+32+8≤(wideSecondMemory p q).byteSize:=by rw[shapes.2.2.2.1];omega
  have first:=write64_end (wideMemory p q) ((scratch p+32)+8).toNat (readI64 (wideMemory p q) (scratch p+68).toNat) j shape.1 fb (by rw[a40];omega)
  have second:=write32_end (wideFirstMemory p q) (scratch p+48).toNat (readI32 (wideFirstMemory p q) (scratch p+76).toNat) j shapes.1 sb (by rw[a48];omega)
  have third:=write64_end (wideSecondMemory p q) ((scratch p).toNat+32) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60)) j shapes.2.2.1 tb (by omega)
  exact third.trans (second.trans (first.trans (wf.trans (savedPrefixMemory_source_byte p q hn hd hheap hroot j hlo hhi))))
/-- Any full word in the original remaining24-byte header is available to
wide decoding from its actual post-prefix input. -/
theorem savedPrefixMemory_source_word (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (offset : Nat) (ho : offset+8≤24) :
    readI64 (savedPrefixMemory p q) ((widePointer p).toNat+offset)=readI64 p.memory ((widePointer p).toNat+offset) := by
  apply readI64_congr_bytes
  intro i hi
  exact savedPrefixMemory_source_byte p q hn hd hheap hroot _ (by omega) (by omega)

theorem savedWideMemory_source_word (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (offset : Nat) (ho : offset+8≤24) :
    readI64 (savedWideMemory p q) ((widePointer p).toNat+offset)=readI64 p.memory ((widePointer p).toNat+offset) := by
  apply readI64_congr_bytes
  intro i hi
  exact savedWideMemory_source_byte p q hn hd hheap hroot _ (by omega) (by omega)

theorem wide_input_bytes (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (i : Nat) (hi : i<16) :
    (savedPrefixMemory p q).read8 ((widePointer p).toNat+i)=p.memory.read8 ((widePointer p).toNat+i) :=
  savedPrefixMemory_source_byte p q hn hd hheap hroot _ (by omega) (by omega)

theorem narrow_input_bytes (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat)
    (i : Nat) (hi : i<8) :
    (savedWideMemory p q).read8 ((narrowPointer p).toNat+i)=p.memory.read8 ((narrowPointer p).toNat+i) := by
  have wide:=header_numbers p hn
  have narrow:=narrow_numbers p hn
  exact savedWideMemory_source_byte p q hn hd hheap hroot _ (by omega) (by omega)

theorem narrow_input_word (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot : (widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat) :
    readI64 (savedWideMemory p q) (narrowPointer p).toNat=readI64 p.memory (narrowPointer p).toNat := by
  apply readI64_congr_bytes
  exact narrow_input_bytes p q hn hd hheap hroot
end WNear.Proofs.StateDecodeBorsh
