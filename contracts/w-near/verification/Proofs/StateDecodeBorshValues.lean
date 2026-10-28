import Proofs.StateDecodeBorshValueCopies
import Proofs.StateDecodeScalarSemantic

/-! Cached425 scalar values are the original remaining header words. Heap and
root separations describe original bytes, rather than post-decoder outcomes. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem add_twice(p:Layout)(hn:Native p)(a b:Nat)(h:a+b<96):
    ((scratch p+UInt32.ofNat a)+UInt32.ofNat b).toNat=(scratch p).toNat+(a+b):=by
  rw[UInt32.add_assoc,←UInt32.ofNat_add]
  exact scratch_add p hn (a+b) h

theorem wide_cached_words(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    wideLow p q=readI64 (wideMemory p q) ((scratch p).toNat+64) ∧
    wideHigh p q=readI64 (wideMemory p q) ((scratch p).toNat+72):=by
  have prev:=savedPrefixMemory_spec p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec true (wideLayout p q) (wide_native p q hn hd)
  change (wideMemory p q).wf ∧(wideMemory p q).byteSize=(savedPrefixMemory p q).byteSize ∧(wideMemory p q).max=(savedPrefixMemory p q).max at shape
  have n:=scratch_numbers p hn
  have h:=ValueCopies.wide_words (wideMemory p q) (scratch p).toNat shape.1 (by rw[shape.2.1,prev.2.1];omega)
  have a40:((scratch p+32)+8).toNat=(scratch p).toNat+40:=add_twice p hn 32 8 (by omega)
  have a44:((scratch p+32)+12).toNat=(scratch p).toNat+44:=add_twice p hn 32 12 (by omega)
  have a48:(scratch p+48).toNat=(scratch p).toNat+48:=scratch_add p hn 48 (by omega)
  have a68:(scratch p+68).toNat=(scratch p).toNat+68:=scratch_add p hn 68 (by omega)
  have a76:(scratch p+76).toNat=(scratch p).toNat+76:=scratch_add p hn 76 (by omega)
  have eq:savedWideMemory p q=ValueCopies.wideSaved (wideMemory p q) (scratch p).toNat:=by
    simp only[savedWideMemory,wideSecondMemory,wideFirstMemory,ValueCopies.wideSaved,ValueCopies.wideSecond,ValueCopies.wideFirst,a40,a48,a68,a76]
  exact ⟨by unfold wideLow;rw[eq];exact h.1,by unfold wideHigh;rw[a44,eq];exact h.2⟩

theorem wide_values_original(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat):
    wideLow p q=readI64 p.memory ((widePointer p).toNat) ∧
    wideHigh p q=readI64 p.memory ((widePointer p).toNat+8):=by
  have wn:=wide_native p q hn hd
  have nums:=scratch_numbers p hn
  have desc:=hn.descriptorAbove
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have ptr:=savedPrefix_descriptor p q hn hd
  have lo:=StateDecodeScalar.finalMemory_low_original true (wideLayout p q) wn (Or.inr (by change (scratch p+56).toNat+16≤p.slice.toNat;rw[a56];omega))
  have hi:=StateDecodeScalar.finalMemory_high_original (wideLayout p q) wn (Or.inr (by change (scratch p+56).toNat+24≤p.slice.toNat;rw[a56];omega))
  change readI64 (wideMemory p q) ((scratch p+56).toNat+8)=readI64 (savedPrefixMemory p q) (readI32 (savedPrefixMemory p q) p.slice.toNat).toNat at lo
  change readI64 (wideMemory p q) ((scratch p+56).toNat+16)=readI64 (savedPrefixMemory p q) ((readI32 (savedPrefixMemory p q) p.slice.toNat).toNat+8) at hi
  rw[a56,ptr.1] at lo hi
  simp only[Nat.add_assoc,Nat.reduceAdd] at lo hi
  have cached:=wide_cached_words p q hn hd
  exact ⟨cached.1.trans (lo.trans (by simpa only[Nat.add_zero] using savedPrefixMemory_source_word p q hn hd hheap hroot 0 (by omega))),cached.2.trans (hi.trans (savedPrefixMemory_source_word p q hn hd hheap hroot 8 (by omega)))⟩

theorem usage_cached_word(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q):
    usageValue p q=readI64 (narrowMemory p q) ((scratch p).toNat+64):=by
  have shape:=narrowMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have copy:=ValueCopies.narrow_word (narrowMemory p q) (scratch p).toNat shape.1 (by rw[shape.2.1];omega)
  have a88:((scratch p+80)+8).toNat=(scratch p).toNat+88:=add_twice p hn 80 8 (by omega)
  have a68:((scratch p+56)+12).toNat=(scratch p).toNat+68:=add_twice p hn 56 12 (by omega)
  have eq:savedNarrowMemory p q=ValueCopies.narrowSaved (narrowMemory p q) (scratch p).toNat:=by
    simp only[savedNarrowMemory,narrowHighMemory,ValueCopies.narrowSaved,ValueCopies.narrowHigh,a88,a68]
  have saved:=savedNarrowMemory_spec p q hn hd
  have high:=vectorHighMemory_spec p q hn hd
  have a8:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have first:=writeI32_spec (savedNarrowMemory p q) (scratch p+8).toNat (vectorLength p q) saved.1 (by rw[a8,saved.2.1];omega)
  have last:=writeI64_spec (vectorHighMemory p q) (scratch p).toNat (vectorPacked p q) high.1 (by rw[high.2.1];omega)
  have frame:usageValue p q=readI64 (savedNarrowMemory p q) ((scratch p).toNat+84):=by
    unfold usageValue
    apply readI64_congr_bytes
    intro i hi
    unfold cachedMemory
    rw[last.2.2.2,ite_eq_right (by omega)]
    unfold vectorHighMemory
    rw[first.2.2.2]
    exact ite_eq_right (by rw[a8];omega)
  rw[eq] at frame
  exact frame.trans copy

theorem usage_value_original(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat):
    usageValue p q=readI64 p.memory (narrowPointer p).toNat:=by
  have nn:=narrow_native p q hn hd
  have nums:=scratch_numbers p hn
  have desc:=hn.descriptorAbove
  have a56:(scratch p+56).toNat=(scratch p).toNat+56:=scratch_add p hn 56 (by omega)
  have ptr:=savedWide_descriptor p q hn hd
  have lo:=StateDecodeScalar.finalMemory_low_original false (narrowLayout p q) nn (Or.inr (by change (scratch p+56).toNat+16≤p.slice.toNat;rw[a56];omega))
  change readI64 (narrowMemory p q) ((scratch p+56).toNat+8)=readI64 (savedWideMemory p q) (readI32 (savedWideMemory p q) p.slice.toNat).toNat at lo
  rw[a56,ptr.1] at lo
  simp only[Nat.add_assoc,Nat.reduceAdd] at lo
  exact (usage_cached_word p q hn hd).trans (lo.trans (narrow_input_word p q hn hd hheap hroot))

theorem scalar_values_original(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat):
    wideLow p q=readI64 p.memory (p.pointer.toNat+4+(count p).toNat) ∧
    wideHigh p q=readI64 p.memory (p.pointer.toNat+4+(count p).toNat+8) ∧
    usageValue p q=readI64 p.memory (p.pointer.toNat+20+(count p).toNat):=by
  have wide:=wide_values_original p q hn hd hheap hroot
  have usage:=usage_value_original p q hn hd hheap hroot
  rw[(header_numbers p hn).1] at wide
  rw[(narrow_numbers p hn).1] at usage
  exact ⟨wide.1,wide.2,usage⟩
end WNear.Proofs.StateDecodeBorsh
