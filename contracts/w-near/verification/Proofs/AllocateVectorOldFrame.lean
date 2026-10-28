import Proofs.AllocateRecordOldFrame
import Proofs.AllocateVectorRecordReadback
import Proofs.AllocateVectorNative

/-! Allocating a fresh vector preserves old bytes above its shadow stack,
except the allocator head and the explicit output record. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 resultMemory finalMemory laidOutMemory

theorem finalMemory_old_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<p.memory.byteSize) (hsp : p.outerSP.toNat≤j)
    (ha : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j)
    (ho : j<p.out686.toNat ∨ p.out686.toNat+8≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have setup := setup_spec p hn
  have bounds := setup_bounds p hn
  rw [(finalMemory_spec p hn).2.2.2.2.2 j ho]
  have child := AllocateRecordCopy.resultMemory_old_frame (layout690 p) (copy_native p hn) j
    (by change j<(laidOutMemory p).byteSize;rw [setup.2.1];exact hj)
    (by change p.sp.toNat≤j;omega) ha
    (by change j<p.out.toNat ∨ p.out.toNat+8≤j;right;rw [nums.2.2.2.2.2.1];omega)
    (by change j<(reservedSP p+8).toNat ∨ (reservedSP p+8).toNat+8≤j;right;rw [nums.2.2.2.2.2.2];omega)
  unfold resultMemory
  rw [child]
  change (laidOutMemory p).read8 j=_
  unfold laidOutMemory
  apply (AllocateLayoutWrapper.final_footprint (layout685 p) hn.allocation.wf bounds.1 bounds.2).2.2.2 j
  · right;rw [nums.2.2.1,nums.2.1];omega
  · right;rw [nums.2.2.2.1];omega
end WNear.Proofs.AllocateVector
