import Proofs.StateDecodeBorshPayloadFrame
import Proofs.StateDecodeBorshOutputFrame
import Proofs.StateDecodePrefixIntervalFrame

/-! Bytes above the original425 frame, advanced descriptor, and caller output
survive every accepted425 memory phase after315. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
private theorem write32_end(m:Memory)(a:Nat)(v:UInt32)(j:Nat)(hw:m.wf)(hb:a+4≤m.byteSize)(he:a+4≤j):
    (writeI32 m a v).read8 j=m.read8 j:=by
  rw[(writeI32_spec m a v hw hb).2.2.2];exact ite_eq_right (by omega)
private theorem write64_end(m:Memory)(a:Nat)(v:UInt64)(j:Nat)(hw:m.wf)(hb:a+8≤m.byteSize)(he:a+8≤j):
    (writeI64 m a v).read8 j=m.read8 j:=by
  rw[(writeI64_spec m a v hw hb).2.2.2];exact ite_eq_right (by omega)

private theorem savedPrefix_interval(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:p.sp425.toNat≤j):
    (savedPrefixMemory p q).read8 j=(prefixMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have shape:=StateDecodePrefixWrapper.finalMemory_spec p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain
  change (prefixMemory p q).wf ∧(prefixMemory p q).byteSize=p.memory.byteSize ∧(prefixMemory p q).max=p.memory.max at shape
  have hi:=writeI32_spec (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) shape.1 (by rw[shape.2.1];omega)
  have high:=write32_end (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q) j shape.1 (by rw[shape.2.1];omega) (by omega)
  have low:=write64_end (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q) j hi.1 (by unfold prefixHighMemory;rw[hi.2.1,shape.2.1];omega) (by omega)
  exact low.trans high

private theorem savedWide_interval(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:p.sp425.toNat≤j)(hdsc:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (savedWideMemory p q).read8 j=(prefixMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have nn:=wide_native p q hn hd
  have orig:=savedPrefixMemory_spec p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) nn
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at shape
  have shapes:=savedWideMemory_specs p q hn hd
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=by rw[UInt32.add_assoc];exact scratch_add p hn 40 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have call:(wideMemory p q).read8 j=(savedPrefixMemory p q).read8 j:=by
    apply StateDecodeScalar.finalMemory_byte_frame true (wideLayout p q) nn j
    · change (scratch p).toNat≤j;omega
    · change j<(scratch p+56).toNat ∨(scratch p+56).toNat+24≤j;right;rw[a56];omega
    · exact hdsc
  have first:=write64_end (wideMemory p q) ((scratch p+32)+8).toNat (readI64 (wideMemory p q) (scratch p+68).toNat) j shape.1 (by rw[a40,shape.2.1,orig.2.1];omega) (by rw[a40];omega)
  have second:=write32_end (wideFirstMemory p q) (scratch p+48).toNat (readI32 (wideFirstMemory p q) (scratch p+76).toNat) j shapes.1 (by rw[a48,shapes.2.1];omega) (by rw[a48];omega)
  have third:=write64_end (wideSecondMemory p q) ((scratch p).toNat+32) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60)) j shapes.2.2.1 (by rw[shapes.2.2.2.1];omega) (by omega)
  exact third.trans (second.trans (first.trans (call.trans (savedPrefix_interval p q hn hd j hj))))

private theorem savedNarrow_interval(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:p.sp425.toNat≤j)(hdsc:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (savedNarrowMemory p q).read8 j=(prefixMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have nn:=narrow_native p q hn hd
  have shape:=narrowMemory_spec p q hn hd
  have high:=narrowHighMemory_spec p q hn hd
  have a88:((scratch p+80)+8).toNat=(scratch p).toNat+88:=by rw[UInt32.add_assoc];exact scratch_add p hn 88 (by omega)
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have call:(narrowMemory p q).read8 j=(savedWideMemory p q).read8 j:=by
    apply StateDecodeScalar.finalMemory_byte_frame false (narrowLayout p q) nn j
    · change (scratch p).toNat≤j;omega
    · change j<(scratch p+56).toNat ∨(scratch p+56).toNat+16≤j;right;rw[a56];omega
    · exact hdsc
  have first:=write32_end (narrowMemory p q) ((scratch p+80)+8).toNat (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat) j shape.1 (by rw[a88,shape.2.1];omega) (by rw[a88];omega)
  have last:=write64_end (narrowHighMemory p q) ((scratch p).toNat+80) (readI64 (narrowHighMemory p q) ((scratch p).toNat+60)) j high.1 (by rw[high.2.1];omega) (by omega)
  exact last.trans (first.trans (call.trans (savedWide_interval p q hn hd j hj hdsc)))

theorem cachedMemory_interval(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:p.sp425.toNat≤j)(hdsc:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (cachedMemory p q).read8 j=(prefixMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have saved:=savedNarrowMemory_spec p q hn hd
  have high:=vectorHighMemory_spec p q hn hd
  have a8:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have first:=write32_end (savedNarrowMemory p q) (scratch p+8).toNat (vectorLength p q) j saved.1 (by rw[a8,saved.2.1];omega) (by rw[a8];omega)
  have last:=write64_end (vectorHighMemory p q) (scratch p).toNat (vectorPacked p q) j high.1 (by rw[high.2.1];omega) (by omega)
  exact last.trans (first.trans (savedNarrow_interval p q hn hd j hj hdsc))


theorem finalMemory_below_head(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hstack:p.sp425.toNat≤j)
    (hheap:j<(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat)
    (hroot:j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hout:j<p.out425.toNat ∨p.out425.toNat+44≤j)
    (hslice:j<p.slice.toNat ∨p.slice.toNat+8≤j):
    (finalMemory p q).read8 j=p.memory.read8 j:=by
  have n:=scratch_numbers p hn
  have sp:p.wrapperSP.toNat=(scratch p).toNat:=congrArg UInt32.toNat hn.childSP
  have out:p.wrapperOut.toNat=(scratch p).toNat+56:=by rw[hn.childOut];exact scratch_add p hn 56 (by omega)
  have inner:p.sp.toNat≤p.wrapperSP.toNat:=by
    rw[hn.prefixNative.childSP]
    change (p.wrapperSP-16).toNat≤p.wrapperSP.toNat
    rw[UInt32.toNat_sub]
    have lo:=hn.spLower
    have lt:=p.wrapperSP.toNat_lt
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have pref:=StateDecodePrefixWrapper.finalMemory_below_head p.toPrefixWrapper q hn.prefixNative hd.toAcceptedDomain j
    (by have lo:=hn.spLower;omega) hheap hroot (Or.inr (by rw[out];omega)) hslice
  exact (finalMemory_cached_byte_frame p q hn hd j hout).trans
    ((cachedMemory_interval p q hn hd j hstack hslice).trans pref)
end WNear.Proofs.StateDecodeBorsh
