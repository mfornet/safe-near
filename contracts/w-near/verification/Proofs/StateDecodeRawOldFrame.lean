import Proofs.StateDecodeRawMemory
import Proofs.AllocatePositiveOldFrame

/-! Original source bytes survive the direct raw allocation when they lie
beyond its original free-block end and outside its real root/output writes. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 laidOutMemory AllocatePositive.finalMemory

private theorem two_bytes (memory : Memory) (a b : Nat) (x y : UInt32) (j : Nat) (hw : memory.wf)
    (ha : a+4≤memory.byteSize) (hb : b+4≤memory.byteSize) (hja : a+4≤j) (hjb : b+4≤j) :
    (writeI32 (writeI32 memory a x) b y).read8 j=memory.read8 j := by
  have first:=writeI32_spec memory a x hw ha
  have second:=writeI32_spec (writeI32 memory a x) b y first.1 (by rw[first.2.1];exact hb)
  rw[second.2.2.2 j,ite_eq_right (show ¬(b≤j ∧ j<b+4) by omega),first.2.2.2 j,
    ite_eq_right (show ¬(a≤j ∧ j<a+4) by omega)]

def originalFinish (p : Layout) := AllocateSearch.finish (AllocatePositive.searchLayout p.toPositive)

/-- The saved search root contains the actual original allocator-head word. -/
theorem original_head_eq (p : Layout) (hn : Native p) :
    AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)=readI32 p.memory p.allocator.toNat := by
  have nums:=AllocatePositive.scratch_numbers p.toPositive hn.allocation
  have self:=PanicAllocateReadback.read_write_self p.memory ((AllocatePositive.scratch p.toPositive).toNat+12)
    (readI32 p.memory p.allocator.toNat) hn.allocation.wf (by omega)
  change readI32 (originalSaved p) (AllocatePositive.scratch p.toPositive+12).toNat=_
  rw [nums.2.1]
  exact self

/-- The free-block end is computed from original memory and its original head;
no stack-save or layout update changes that header. -/
theorem original_finish_eq (p : Layout) (hn : Native p) :
    originalFinish p=Allocate.endWord p.memory (readI32 p.memory p.allocator.toNat) := by
  have nums:=AllocatePositive.scratch_numbers p.toPositive hn.allocation
  have stack:=stack_numbers p hn
  have lo:=hn.spLower
  have ha : p.spRaw.toNat≤(readI32 p.memory p.allocator.toNat).toNat := by
    rw [←original_head_eq p hn]
    exact hn.headAbove
  have frame:=PanicAllocateReadback.read_write_frame p.memory (readI32 p.memory p.allocator.toNat).toNat
    ((AllocatePositive.scratch p.toPositive).toNat+12) (readI32 p.memory p.allocator.toNat) hn.allocation.wf (by omega)
    (Or.inr (by rw[stack.2.2.2.2.1];omega))
  change Allocate.endWord (originalSaved p) (AllocateSearch.head (AllocatePositive.searchLayout p.toPositive))=_
  rw [original_head_eq p hn]
  unfold Allocate.endWord originalSaved AllocatePositive.savedMemory
  rw [frame]

theorem actual_finish_eq (p : Layout) (hn : Native p) :
    AllocateSearch.finish (AllocatePositive.searchLayout (actualPositive p))=originalFinish p := by
  change Allocate.endWord (actualSaved p) (AllocateSearch.head (AllocatePositive.searchLayout (actualPositive p)))=
    Allocate.endWord (originalSaved p) (AllocateSearch.head (AllocatePositive.searchLayout p.toPositive))
  rw[saved_head p hn]
  unfold Allocate.endWord
  rw[saved_word p hn _ hn.headAbove]

/-- The requested allocation lies wholly before the original free-block end.
This separates its writes from source bytes at or beyond that end. -/
theorem result_finish_bound (p : Layout) (hn : Native p) : (result p).toNat+p.size.toNat≤(originalFinish p).toNat := by
  have h:=AllocatePositive.result_finish_bound (actualPositive p) (allocation_native p hn)
  rw[actual_finish_eq p hn] at h
  exact h

theorem layout_byte_frame (p : Layout) (hn : Native p) (j : Nat) (hsp : p.spRaw.toNat≤j) :
    (laidOutMemory p).read8 j=p.memory.read8 j := by
  have bounds:=layout_bounds p hn
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have h:=AllocateLayoutWrapper.final_footprint (layout752 p) hn.allocation.wf bounds.1 bounds.2
  unfold laidOutMemory
  exact h.2.2.2 j (Or.inr (by rw[n.2.2.1];omega)) (Or.inr (by rw[n.2.2.2.1];omega))

theorem allocated_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hsp : p.spRaw.toNat≤j) (hend : (originalFinish p).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j) :
    (allocatedMemory p).read8 j=p.memory.read8 j := by
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have upper:=p.spRaw.toNat_lt
  have lower : p.sp.toNat≤j := by
    rw[hn.childSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have heap : (AllocateSearch.finish (AllocatePositive.searchLayout (actualPositive p))).toNat+8≤j := by
    rw[actual_finish_eq p hn];exact hend
  have h:=AllocatePositive.finalMemory_byte_frame (actualPositive p) (allocation_native p hn) j lower heap hroot
  exact h.trans (layout_byte_frame p hn j hsp)

theorem memory769_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hsp : p.spRaw.toNat≤j) (hend : (originalFinish p).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j) :
    (memory769 p).read8 j=p.memory.read8 j := by
  have a:=allocated_spec p hn
  have b:=memory770_spec p hn
  have n:=record_numbers p hn
  have lo:=hn.spLower
  have hi:=hn.spBound
  have f770 : (memory770 p).read8 j=(allocatedMemory p).read8 j := by
    unfold memory770 highMemory770
    apply two_bytes _ _ _ _ _ j a.1
    all_goals first |(rw[a.2.1,n.1];omega) |(rw[n.1];omega)
  have f769 : (memory769 p).read8 j=(memory770 p).read8 j := by
    unfold memory769 lowMemory769
    apply two_bytes _ _ _ _ _ j b.1
    all_goals first |(rw[b.2.1,n.2.1];omega) |(rw[n.2.1];omega)
  exact f769.trans (f770.trans (allocated_byte_frame p hn j hsp hend hroot))

/-- The complete raw result preserves original source bytes. Caller output
separation is explicit; it is unnecessary only for cached record readback. -/
theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hsp : p.spRaw.toNat≤j) (hend : (originalFinish p).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j)
    (hout : j<p.outRaw.toNat ∨ p.outRaw.toNat+8≤j) :
    (finalMemory p).read8 j=p.memory.read8 j :=
  ((finalMemory_spec p hn).2.2.2.2.2 j hout).trans (memory769_byte_frame p hn j hsp hend hroot)
end WNear.Proofs.StateDecodeRaw
