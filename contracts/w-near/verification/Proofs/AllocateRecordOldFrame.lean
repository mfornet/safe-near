import Proofs.AllocateRetryOldFrame
import Proofs.AllocateRecordResources
import Proofs.AllocateRecordCopyResources

/-! Old-memory frames through zero-fill and the actual allocation result copies. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 finalMemory

theorem finalMemory_old_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<p.memory.byteSize) (hsp : p.sp.toNat≤j)
    (ha : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have span := AllocateRetry.result_above_original p.toRetry hn
  have fill := finalMemory_spec p hn
  rw [fill.2.2.2 j,ite_eq_right (show ¬((result p).toNat≤j ∧ j<(result p).toNat+p.size.toNat) by
    change p.memory.byteSize≤(result p).toNat at span;omega)]
  exact AllocateRetry.finalMemory_old_frame p.toRetry hn j hj hsp ha
end WNear.Proofs.AllocateZeroedRetry

namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem finalMemory_old_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<p.memory.byteSize) (hsp : p.sp.toNat≤j)
    (ha : j<p.allocator.toNat ∨ p.allocator.toNat+4≤j)
    (ho : j<p.out.toNat ∨ p.out.toNat+8≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  rw [(finalMemory_spec p hn).2.2.2.2.2 j ho]
  exact AllocateZeroedRetry.finalMemory_old_frame p.toZeroed hn.allocation j hj hsp ha
end WNear.Proofs.AllocateRecord

namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem resultMemory_old_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<p.inner.memory.byteSize) (hsp : p.inner.sp.toNat≤j)
    (ha : j<p.inner.allocator.toNat ∨ p.inner.allocator.toNat+4≤j)
    (hi : j<p.inner.out.toNat ∨ p.inner.out.toNat+8≤j)
    (ho : j<p.out.toNat ∨ p.out.toNat+8≤j) :
    (resultMemory p).read8 j=p.inner.memory.read8 j := by
  have a := AllocateRecord.finalMemory_spec p.inner hn.inner
  have b := AllocateRecord.allocated_spec p.inner hn.inner
  have hb : p.out.toNat+8≤(allocatedMemory p).byteSize := by
    change p.out.toNat+8≤(AllocateRecord.finalMemory p.inner).byteSize
    rw [a.2.1]
    have bound := hn.outputBound
    omega
  rw [show resultMemory p=finalMemory (allocatedMemory p) p.out p.inner.sp from rfl,
    finalMemory_outside (allocatedMemory p) p.out p.inner.sp a.1 hb j ho]
  exact AllocateRecord.finalMemory_old_frame p.inner hn.inner j hj hsp ha hi
end WNear.Proofs.AllocateRecordCopy
