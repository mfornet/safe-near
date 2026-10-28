import Proofs.AllocatePositivePayload
import Proofs.AllocateSearchOldFrame

/-! Direct581 frames old bytes beyond the original free block, apart from the
actual stack-save and allocator-root words. Requested payload ends by `finish`. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 savedMemory searchedMemory finalMemory AllocateSearch.finalMemory

theorem result_finish_bound (p : Layout) (hn : Native p) :
    (result p).toNat+p.size.toNat≤(AllocateSearch.finish (searchLayout p)).toNat := by
  have hp:=Allocate.split_pointer_toNat (searchLayout p).memory (AllocateSearch.head (searchLayout p))
    (searchLayout p).words hn.search.split
  have count:=requested_le_words p hn
  have room:=hn.search.split.room
  change (result p).toNat=(AllocateSearch.finish (searchLayout p)).toNat-(words p).toNat*4 at hp
  change (AllocateSearch.head (searchLayout p)).toNat+80+(words p).toNat*4≤(AllocateSearch.finish (searchLayout p)).toNat at room
  omega

theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hstack : p.sp.toNat≤j) (hheap : (AllocateSearch.finish (searchLayout p)).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have nums:=scratch_numbers p hn
  have lo:=hn.spLower
  have saved:=writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat)
    hn.wf (by omega)
  have savedByte : (savedMemory p).read8 j=p.memory.read8 j := by
    unfold savedMemory
    rw [saved.2.2.2 j]
    apply ite_eq_right
    omega
  have search:=AllocateSearch.final_shape (searchLayout p) hn.search
  have savedSize : (savedMemory p).byteSize=p.memory.byteSize := by simpa only [savedMemory] using saved.2.1
  have searchWf : (searchedMemory p).wf := by simpa only [searchedMemory] using search.wf
  have finalBound : p.allocator.toNat+4≤(searchedMemory p).byteSize := by
    unfold searchedMemory
    rw [search.size]
    change p.allocator.toNat+4≤(savedMemory p).byteSize
    rw [savedSize]
    exact hn.allocatorBound
  have written:=writeI32_spec (searchedMemory p) p.allocator.toNat
    (readI32 (searchedMemory p) ((scratch p).toNat+12)) searchWf finalBound
  have frame:=AllocateSearch.finalMemory_byte_frame (searchLayout p) hn.search j (Or.inr hheap)
  unfold finalMemory
  rw [written.2.2.2 j,ite_eq_right (show ¬(p.allocator.toNat≤j ∧ j<p.allocator.toNat+4) by omega)]
  simpa only [searchedMemory] using frame.trans savedByte
end WNear.Proofs.AllocatePositive
