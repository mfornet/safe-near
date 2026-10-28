import Proofs.StateDecodeRawOldFrame
import Proofs.AllocatePositiveIntervalFrame

/-! Actual raw767 frames bytes both below and beyond its original free block. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 laidOutMemory AllocatePositive.finalMemory

theorem result_head_bound (p:Layout)(hn:Native p):
    (AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat≤(result p).toNat:=by
  have h:=AllocatePositive.result_head_bound (actualPositive p) (allocation_native p hn)
  rw[saved_head p hn] at h
  exact h

private theorem two_bytes (memory : Memory) (a b : Nat) (x y : UInt32) (j : Nat) (hw : memory.wf)
    (ha : a+4≤memory.byteSize) (hb : b+4≤memory.byteSize) (hja : a+4≤j) (hjb : b+4≤j) :
    (writeI32 (writeI32 memory a x) b y).read8 j=memory.read8 j := by
  have first:=writeI32_spec memory a x hw ha
  have second:=writeI32_spec (writeI32 memory a x) b y first.1 (by rw[first.2.1];exact hb)
  rw[second.2.2.2 j,ite_eq_right (show ¬(b≤j ∧ j<b+4) by omega),first.2.2.2 j,
    ite_eq_right (show ¬(a≤j ∧ j<a+4) by omega)]

theorem allocated_interval_frame (p : Layout) (hn : Native p) (j : Nat)
    (hsp : p.spRaw.toNat≤j) (hend : j<(AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat ∨ (originalFinish p).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j) :
    (allocatedMemory p).read8 j=p.memory.read8 j := by
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have upper:=p.spRaw.toNat_lt
  have lower : p.sp.toNat≤j := by
    rw[hn.childSP,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have heap : j<(AllocateSearch.head (AllocatePositive.searchLayout (actualPositive p))).toNat ∨ (AllocateSearch.finish (AllocatePositive.searchLayout (actualPositive p))).toNat+8≤j := by
    rw[saved_head p hn,actual_finish_eq p hn];exact hend
  have h:=AllocatePositive.finalMemory_interval_frame (actualPositive p) (allocation_native p hn) j lower heap hroot
  exact h.trans (layout_byte_frame p hn j hsp)

theorem memory769_interval_frame (p : Layout) (hn : Native p) (j : Nat)
    (hsp : p.spRaw.toNat≤j) (hend : j<(AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat ∨ (originalFinish p).toNat+8≤j)
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
  exact f769.trans (f770.trans (allocated_interval_frame p hn j hsp hend hroot))

/-- The complete raw result preserves original source bytes. Caller output
separation is explicit; it is unnecessary only for cached record readback. -/
theorem finalMemory_interval_frame (p : Layout) (hn : Native p) (j : Nat)
    (hsp : p.spRaw.toNat≤j) (hend : j<(AllocateSearch.head (AllocatePositive.searchLayout p.toPositive)).toNat ∨ (originalFinish p).toNat+8≤j)
    (hroot : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j)
    (hout : j<p.outRaw.toNat ∨ p.outRaw.toNat+8≤j) :
    (finalMemory p).read8 j=p.memory.read8 j :=
  ((finalMemory_spec p hn).2.2.2.2.2 j hout).trans (memory769_interval_frame p hn j hsp hend hroot)
end WNear.Proofs.StateDecodeRaw
