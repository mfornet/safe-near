import Proofs.StateDecodeBorshOutputFrame
import Proofs.StateDecodeScalarSliceOutput

/-! The actual425 remaining slice, including the original29-byte header's
exhausted-input case. Final caller output/slice separation is explicit. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64 finalMemory cachedMemory vectorHighMemory savedNarrowMemory narrowHighMemory narrowMemory
private theorem write32_end(m:Memory)(a:Nat)(v:UInt32)(j:Nat)(hw:m.wf)(hb:a+4≤m.byteSize)(he:a+4≤j):
    (writeI32 m a v).read8 j=m.read8 j:=by
  rw[(writeI32_spec m a v hw hb).2.2.2];exact ite_eq_right (by omega)
private theorem write64_end(m:Memory)(a:Nat)(v:UInt64)(j:Nat)(hw:m.wf)(hb:a+8≤m.byteSize)(he:a+8≤j):
    (writeI64 m a v).read8 j=m.read8 j:=by
  rw[(writeI64_spec m a v hw hb).2.2.2];exact ite_eq_right (by omega)

theorem cachedMemory_narrow_byte(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (j:Nat)(hj:p.sp425.toNat≤j):(cachedMemory p q).read8 j=(narrowMemory p q).read8 j:=by
  have n:=scratch_numbers p hn
  have a88:((scratch p+80)+8).toNat=(scratch p).toNat+88:=by
    have eq:(scratch p+80)+8=scratch p+88:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 88 (by omega)
  have a8:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have spec0:=narrowMemory_spec p q hn hd
  have b0:((scratch p+80)+8).toNat+4≤(narrowMemory p q).byteSize:=by rw[spec0.2.1,a88];omega
  have f0:(narrowHighMemory p q).read8 j=(narrowMemory p q).read8 j:=by
    unfold narrowHighMemory
    exact write32_end (narrowMemory p q) ((scratch p+80)+8).toNat (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat) j spec0.1 b0 (by rw[a88];omega)
  have spec1:=narrowHighMemory_spec p q hn hd
  have b1:((scratch p).toNat+80)+8≤(narrowHighMemory p q).byteSize:=by rw[spec1.2.1];omega
  have f1:(savedNarrowMemory p q).read8 j=(narrowHighMemory p q).read8 j:=by
    unfold savedNarrowMemory
    exact write64_end (narrowHighMemory p q) ((scratch p).toNat+80) (readI64 (narrowHighMemory p q) ((scratch p).toNat+60)) j spec1.1 b1 (by omega)
  have spec2:=savedNarrowMemory_spec p q hn hd
  have b2:(scratch p+8).toNat+4≤(savedNarrowMemory p q).byteSize:=by rw[spec2.2.1,a8];omega
  have f2:(vectorHighMemory p q).read8 j=(savedNarrowMemory p q).read8 j:=by
    unfold vectorHighMemory
    exact write32_end (savedNarrowMemory p q) (scratch p+8).toNat (vectorLength p q) j spec2.1 b2 (by rw[a8];omega)
  have spec3:=vectorHighMemory_spec p q hn hd
  have b3:(scratch p).toNat+8≤(vectorHighMemory p q).byteSize:=by rw[spec3.2.1];omega
  have f3:(cachedMemory p q).read8 j=(vectorHighMemory p q).read8 j:=by
    unfold cachedMemory
    exact write64_end (vectorHighMemory p q) (scratch p).toNat (vectorPacked p q) j spec3.1 b3 (by omega)
  exact f3.trans (f2.trans (f1.trans f0))

theorem finalMemory_slice_words(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hs:p.out425.toNat+44≤p.slice.toNat ∨p.slice.toNat+8≤p.out425.toNat):
    readI32 (finalMemory p q) p.slice.toNat=narrowPointer p+8 ∧
    readI32 (finalMemory p q) (p.slice.toNat+4)=narrowLength p-8:=by
  have nn:=narrow_native p q hn hd
  have n:=scratch_numbers p hn
  have above:=hn.descriptorAbove
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have sep:(narrowLayout p q).out.toNat+4≤(narrowLayout p q).slice.toNat ∨
      (narrowLayout p q).slice.toNat+8≤(narrowLayout p q).out.toNat:=by
    left;change (scratch p+56).toNat+4≤p.slice.toNat;rw[a56];omega
  have words:=StateDecodeScalar.finalMemory_slice_words false (narrowLayout p q) nn sep
  have memory:StateDecodeScalar.finalMemory false (narrowLayout p q)=narrowMemory p q:=by unfold narrowMemory;rfl
  rw[memory] at words
  change readI32 (narrowMemory p q) p.slice.toNat=readI32 (savedWideMemory p q) p.slice.toNat+8 ∧
    readI32 (narrowMemory p q) (p.slice.toNat+4)=readI32 (savedWideMemory p q) (p.slice.toNat+4)-8 at words
  have desc:=savedWide_descriptor p q hn hd
  rw[desc.1,desc.2] at words
  have frame(address:Nat)(ha:p.slice.toNat≤address)(hb:address+4≤p.slice.toNat+8):
      readI32 (finalMemory p q) address=readI32 (narrowMemory p q) address:=by
    apply readI32_congr_bytes
    intro i hi
    have out:address+i<p.out425.toNat ∨p.out425.toNat+44≤address+i:=by
      rcases hs with h|h
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    exact (finalMemory_cached_byte_frame p q hn hd (address+i) out).trans
      (cachedMemory_narrow_byte p q hn hd (address+i) (by omega))
  exact ⟨(frame _ (by omega) (by omega)).trans words.1,(frame _ (by omega) (by omega)).trans words.2⟩

theorem finalMemory_exhausted_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hs:p.out425.toNat+44≤p.slice.toNat ∨p.slice.toNat+8≤p.out425.toNat)
    (hc:count p=1)(hl:p.length=29):
    readI32 (finalMemory p q) p.slice.toNat=p.pointer+29 ∧
    readI32 (finalMemory p q) (p.slice.toNat+4)=0:=by
  have words:=finalMemory_slice_words p q hn hd hs
  have ptr:narrowPointer p+8=p.pointer+29:=by
    unfold narrowPointer widePointer StateDecodePrefix.payloadPointer
    rw[hc]
    simp only[UInt32.add_assoc]
    rfl
  have len:narrowLength p-8=0:=by
    change ((p.length-4)-count p)-16-8=0
    rw[hl,hc]
    rfl
  rw[ptr,len] at words
  exact words
end WNear.Proofs.StateDecodeBorsh
