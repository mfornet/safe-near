import Proofs.StateDecodeBorshOutputRecord
import Proofs.StateDecodeBorshSourceFrame
import Proofs.StateDecodePrefixWrapperRecord
import Proofs.StorePairReadback

/-! The saved vector record survives both scalar readers and the literal
scratch copies; the final cache retains the canonical315 prefix fields. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem frame32(m:Memory)(a:Nat)(v:UInt32)(j:Nat)(hw:m.wf)(hb:a+4≤m.byteSize)
    (hs:j<a ∨a+4≤j):(writeI32 m a v).read8 j=m.read8 j:=by
  rw[(writeI32_spec m a v hw hb).2.2.2]
  exact ite_eq_right (by rcases hs with h|h <;> omega)
private theorem frame64(m:Memory)(a:Nat)(v:UInt64)(j:Nat)(hw:m.wf)(hb:a+8≤m.byteSize)
    (hs:j<a ∨a+8≤j):(writeI64 m a v).read8 j=m.read8 j:=by
  rw[(writeI64_spec m a v hw hb).2.2.2]
  exact ite_eq_right (by rcases hs with h|h <;> omega)

private theorem savedWide_prefix_byte(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:(scratch p).toNat+16≤j)(he:j<(scratch p).toNat+28):
    (savedWideMemory p q).read8 j=(savedPrefixMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have sn:=wide_native p q hn hd
  have shape:=savedPrefixMemory_spec p q hn hd
  have wide:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) sn
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at wide
  have ws:=savedWideMemory_specs p q hn hd
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=by
    rw[UInt32.add_assoc];exact scratch_add p hn 40 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have scalar:(wideMemory p q).read8 j=(savedPrefixMemory p q).read8 j:=by
    apply StateDecodeScalar.finalMemory_byte_frame true (wideLayout p q) sn j
    · change (scratch p).toNat≤j;omega
    · change j<(scratch p+56).toNat ∨(scratch p+56).toNat+24≤j;left;rw[a56];omega
    · change j<p.slice.toNat ∨p.slice.toNat+8≤j;left;have h:=hn.descriptorAbove;omega
  have f:=frame64 (wideMemory p q) ((scratch p+32)+8).toNat (readI64 (wideMemory p q) (scratch p+68).toNat) j wide.1 (by rw[a40,wide.2.1,shape.2.1];omega) (Or.inl (by rw[a40];omega))
  have s:=frame32 (wideFirstMemory p q) (scratch p+48).toNat (readI32 (wideFirstMemory p q) (scratch p+76).toNat) j ws.1 (by rw[a48,ws.2.1];omega) (Or.inl (by rw[a48];omega))
  have l:=frame64 (wideSecondMemory p q) ((scratch p).toNat+32) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60)) j ws.2.2.1 (by rw[ws.2.2.2.1];omega) (Or.inl (by omega))
  exact l.trans (s.trans (f.trans scalar))

theorem savedNarrow_prefix_byte(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:(scratch p).toNat+16≤j)(he:j<(scratch p).toNat+28):
    (savedNarrowMemory p q).read8 j=(savedPrefixMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have nn:=narrow_native p q hn hd
  have shape:=narrowMemory_spec p q hn hd
  have high:=narrowHighMemory_spec p q hn hd
  have a88:((scratch p+80)+8).toNat=(scratch p).toNat+88:=by
    rw[UInt32.add_assoc];exact scratch_add p hn 88 (by omega)
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have scalar:(narrowMemory p q).read8 j=(savedWideMemory p q).read8 j:=by
    apply StateDecodeScalar.finalMemory_byte_frame false (narrowLayout p q) nn j
    · change (scratch p).toNat≤j;omega
    · change j<(scratch p+56).toNat ∨(scratch p+56).toNat+16≤j;left;rw[a56];omega
    · change j<p.slice.toNat ∨p.slice.toNat+8≤j;left;have h:=hn.descriptorAbove;omega
  have h:=frame32 (narrowMemory p q) ((scratch p+80)+8).toNat (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat) j shape.1 (by rw[a88,shape.2.1];omega) (Or.inl (by rw[a88];omega))
  have l:=frame64 (narrowHighMemory p q) ((scratch p).toNat+80) (readI64 (narrowHighMemory p q) ((scratch p).toNat+60)) j high.1 (by rw[high.2.1];omega) (Or.inl (by omega))
  exact l.trans (h.trans (scalar.trans (savedWide_prefix_byte p q hn hd j hj he)))

theorem vectorPacked_eq_prefixPacked(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    vectorPacked p q=prefixPacked p q:=by
  have n:=scratch_numbers p hn
  have saved:=savedNarrowMemory_spec p q hn hd
  have a8:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have high:=writeI32_spec (savedNarrowMemory p q) (scratch p+8).toNat (vectorLength p q) saved.1 (by rw[a8,saved.2.1];omega)
  have prior:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  change (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize ∧(prefixMemory p q).max=p.memory.max at prior
  have first:=writeI32_spec (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) prior.1 (by rw[prior.2.1];omega)
  have last:=writeI64_spec (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q) first.1 (by unfold prefixHighMemory;rw[first.2.1,prior.2.1];omega)
  unfold vectorPacked
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  unfold vectorHighMemory
  rw[high.2.2.2,ite_eq_right (by rw[a8];omega)]
  rw[savedNarrow_prefix_byte p q hn hd _ (by omega) (by omega)]
  unfold savedPrefixMemory
  rw[last.2.2.2,ite_eq_left (by omega)]
  congr 2
  omega

theorem vectorLength_eq_prefixLength(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    vectorLength p q=prefixLength p q:=by
  have n:=scratch_numbers p hn
  have a24:((scratch p+16)+8).toNat=(scratch p).toNat+24:=by
    rw[UInt32.add_assoc];exact scratch_add p hn 24 (by omega)
  have prior:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  change (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize ∧(prefixMemory p q).max=p.memory.max at prior
  have first:=writeI32_spec (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) prior.1 (by rw[prior.2.1];omega)
  have last:=writeI64_spec (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q) first.1 (by unfold prefixHighMemory;rw[first.2.1,prior.2.1];omega)
  have frame:vectorLength p q=readI32 (prefixHighMemory p q) ((scratch p).toNat+24):=by
    unfold vectorLength;rw[a24]
    apply Allocate.readI32_congr_bytes
    intro i hi
    rw[savedNarrow_prefix_byte p q hn hd _ (by omega) (by omega)]
    unfold savedPrefixMemory
    rw[last.2.2.2]
    exact ite_eq_right (by omega)
  exact frame.trans (PanicAllocateReadback.read_write_self (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) prior.1 (by rw[prior.2.1];omega))

private theorem prefix_record_words(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    readI32 (prefixMemory p q) ((scratch p).toNat+60)=StateDecodePrefix.payloadAddress p.toPrefix q ∧
    readI32 (prefixMemory p q) ((scratch p).toNat+64)=count p ∧
    readI32 (prefixMemory p q) ((scratch p).toNat+68)=count p:=by
  have n:=scratch_numbers p hn
  have above:=hn.descriptorAbove
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have small:(StateDecodePrefixWrapper.scratch p.toPrefixWrapper).toNat=(scratch p).toNat-16:=by
    unfold StateDecodePrefixWrapper.scratch
    rw[hn.childSP,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have lo:=hn.spLower
    have lt:=(scratch p).toNat_lt
    omega
  have child:p.out.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat:=by
    left;rw[hn.prefixNative.childOut,small];omega
  have out:p.wrapperOut.toNat+16≤p.slice.toNat ∨p.slice.toNat+8≤p.wrapperOut.toNat:=by
    left;rw[hn.childOut,a56];omega
  have record:=StateDecodePrefixWrapper.finalMemory_record p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain child out
  have r:p.wrapperOut.toNat=(scratch p).toNat+56:=by rw[hn.childOut,a56]
  rw[r] at record
  simp only[Nat.add_assoc,Nat.reduceAdd] at record
  exact ⟨record.2.1,record.2.2.1,record.2.2.2.1⟩

theorem vectorLength_eq_count(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    vectorLength p q=count p:=by
  have a68:(scratch p+68).toNat=(scratch p).toNat+68:=scratch_add p hn 68 (by omega)
  have old:=prefix_record_words p q hn hd
  rw[vectorLength_eq_prefixLength p q hn hd,prefixLength,a68]
  exact old.2.2

private theorem word_halves(m:Memory)(a:Nat):
    UInt32.ofNat (readI64 m a).toNat=readI32 m a ∧
    UInt32.ofNat ((readI64 m a).toNat >>>32)=readI32 m (a+4):=by
  have b:∀i,(m.read8 (a+i)).toNat<256:=fun i=>UInt8.toNat_lt _
  have b0:=b 0;have b1:=b 1;have b2:=b 2;have b3:=b 3
  have b4:=b 4;have b5:=b 5;have b6:=b 6;have b7:=b 7
  constructor <;> apply UInt32.toNat_inj.mp <;>
    simp [readI64,readI32,List.range_succ,Nat.shiftRight_eq_div_pow,Nat.add_assoc] <;>
    simp only[Nat.add_zero] at * <;> omega

theorem vectorPacked_halves(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    UInt32.ofNat (vectorPacked p q).toNat=StateDecodePrefix.payloadAddress p.toPrefix q ∧
    UInt32.ofNat ((vectorPacked p q).toNat >>>32)=count p:=by
  rw[vectorPacked_eq_prefixPacked p q hn hd]
  have halves:=word_halves (prefixMemory p q) ((scratch p).toNat+60)
  have words:=prefix_record_words p q hn hd
  simp only[Nat.add_assoc,Nat.reduceAdd] at halves
  exact ⟨halves.1.trans words.1,halves.2.trans words.2.1⟩

theorem final_vector_record(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    readI32 (finalMemory p q) (p.out425.toNat+32)=StateDecodePrefix.payloadAddress p.toPrefix q ∧
    readI32 (finalMemory p q) (p.out425.toNat+36)=count p ∧
    readI32 (finalMemory p q) (p.out425.toNat+40)=count p:=by
  have record:=finalMemory_record p q hn hd
  have halves:=word_halves (finalMemory p q) (p.out425.toNat+32)
  rw[record.2.2.2.2.1] at halves
  simp only[Nat.add_assoc,Nat.reduceAdd] at halves
  have values:=vectorPacked_halves p q hn hd
  exact ⟨halves.1.symm.trans values.1,halves.2.symm.trans values.2,
    record.2.2.2.2.2.trans (vectorLength_eq_count p q hn hd)⟩
end WNear.Proofs.StateDecodeBorsh
