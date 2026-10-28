import Proofs.StateDecodeBorshMemoryNative

/-! All three actual425 guard tags are derived from preceding callees and
sequential saves. No post-call tag or execution result is an assumption. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem word64_frame (memory : Memory) (address dest : Nat) (value : UInt64)
    (hw : memory.wf) (hb : dest+8≤memory.byteSize)
    (hsep : address+4≤dest ∨dest+8≤address) :
    readI32 (writeI64 memory dest value) address=readI32 memory address := by
  have spec:=writeI64_spec memory dest value hw hb
  apply Allocate.readI32_congr_bytes
  intro i hi
  rw[spec.2.2.2]
  have no:¬(dest≤address+i ∧address+i<dest+8):=by rcases hsep with h|h <;> omega
  exact ite_eq_right no

theorem prefixMemory_tag (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    readI32 (prefixMemory p q) ((scratch p).toNat+56)=0 := by
  have record:=StateDecodePrefixWrapper.Tail.finalMemory_record
    (StateDecodePrefixWrapper.tailLayout p.toPrefixWrapper q)
    (StateDecodePrefixWrapper.tail_native p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain)
  have tag:readI32 (prefixMemory p q) p.wrapperOut.toNat=0:=record.1
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  rw[hn.childOut,a56] at tag
  exact tag

theorem savedWideMemory_tag (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    readI32 (savedWideMemory p q) ((scratch p).toNat+56)=0 := by
  have native:=wide_native p q hn hd
  have prev:=savedPrefixMemory_spec p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) native
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at shape
  have shapes:=savedWideMemory_specs p q hn hd
  have n:=scratch_numbers p hn
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=by
    have eq:(scratch p+32)+8=scratch p+40:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 40 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have fb:((scratch p+32)+8).toNat+8≤(wideMemory p q).byteSize:=by rw[a40,shape.2.1,prev.2.1];omega
  have sb:(scratch p+48).toNat+4≤(wideFirstMemory p q).byteSize:=by rw[a48,shapes.2.1];omega
  have tb:(scratch p).toNat+32+8≤(wideSecondMemory p q).byteSize:=by rw[shapes.2.2.2.1];omega
  have first:=word64_frame (wideMemory p q) ((scratch p).toNat+56) ((scratch p+32)+8).toNat
    (readI64 (wideMemory p q) (scratch p+68).toNat) shape.1 fb (Or.inr (by rw[a40];omega))
  have second:=PanicAllocateReadback.read_write_frame (wideFirstMemory p q) ((scratch p).toNat+56) (scratch p+48).toNat
    (readI32 (wideFirstMemory p q) (scratch p+76).toNat) shapes.1 sb (Or.inr (by rw[a48];omega))
  have third:=word64_frame (wideSecondMemory p q) ((scratch p).toNat+56) ((scratch p).toNat+32)
    (readI64 (wideSecondMemory p q) ((scratch p).toNat+60)) shapes.2.2.1 tb (Or.inr (by omega))
  have tag:=StateDecodeScalar.finalMemory_tag true (wideLayout p q) native
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have normalized:readI32 (wideMemory p q) ((scratch p).toNat+56)=0:=by
    simpa only[wideLayout,wideMemory,a56] using tag
  exact third.trans (second.trans (first.trans normalized))

theorem savedNarrowMemory_tag (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    readI32 (savedNarrowMemory p q) ((scratch p).toNat+56)=0 := by
  have native:=narrow_native p q hn hd
  have shape:=narrowMemory_spec p q hn hd
  have highShape:=narrowHighMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a88:((scratch p+80)+8).toNat=(scratch p).toNat+88:=by
    have eq:(scratch p+80)+8=scratch p+88:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 88 (by omega)
  have hb:((scratch p+80)+8).toNat+4≤(narrowMemory p q).byteSize:=by rw[a88,shape.2.1];omega
  have lb:(scratch p).toNat+80+8≤(narrowHighMemory p q).byteSize:=by rw[highShape.2.1];omega
  have high:=PanicAllocateReadback.read_write_frame (narrowMemory p q) ((scratch p).toNat+56) ((scratch p+80)+8).toNat
    (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat) shape.1 hb (Or.inl (by rw[a88];omega))
  have low:=word64_frame (narrowHighMemory p q) ((scratch p).toNat+56) ((scratch p).toNat+80)
    (readI64 (narrowHighMemory p q) ((scratch p).toNat+60)) highShape.1 lb (Or.inl (by omega))
  have tag:=StateDecodeScalar.finalMemory_tag false (narrowLayout p q) native
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have normalized:readI32 (narrowMemory p q) ((scratch p).toNat+56)=0:=by
    simpa only[narrowLayout,narrowMemory,a56] using tag
  exact low.trans (high.trans normalized)
end WNear.Proofs.StateDecodeBorsh
