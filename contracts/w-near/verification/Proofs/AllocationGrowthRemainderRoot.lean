import Proofs.AllocationGrowthRemainderFrames

/-! The allocator root is preserved after the real allocation when result-record
writes are separated from it. These are original address conditions. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem finalMemory_allocation_frame(p:Layout)(hn:Native p)(j:Nat)
    (before:j<(result p).toNat)(outside:j<p.out.toNat ∨p.out.toNat+8≤j):
    (finalMemory p).read8 j=(AllocateRetry.finalMemory p.toZeroed.toRetry).read8 j:=by
  rw[(finalMemory_spec p hn).2.2.2.2.2 j outside]
  exact AllocateZeroedRetry.finalMemory_before_payload p.toZeroed hn.allocation j before
end WNear.Proofs.AllocateRecord

namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem resultMemory_allocation_frame(p:Layout)(hn:Native p)(j:Nat)
    (before:j<(AllocateRecord.result p.inner).toNat)
    (innerOutside:j<p.inner.out.toNat ∨p.inner.out.toNat+8≤j)
    (outside:j<p.out.toNat ∨p.out.toNat+8≤j):
    (resultMemory p).read8 j=(AllocateRetry.finalMemory p.inner.toZeroed.toRetry).read8 j:=by
  have a:=AllocateRecord.finalMemory_spec p.inner hn.inner
  have b:=AllocateRecord.allocated_spec p.inner hn.inner
  have hb:p.out.toNat+8≤(allocatedMemory p).byteSize:=by
    change p.out.toNat+8≤(AllocateRecord.finalMemory p.inner).byteSize
    rw[a.2.1]
    have bound:=hn.outputBound
    omega
  rw[show resultMemory p=finalMemory (allocatedMemory p) p.out p.inner.sp from rfl,
    finalMemory_outside (allocatedMemory p) p.out p.inner.sp a.1 hb j outside]
  exact AllocateRecord.finalMemory_allocation_frame p.inner hn.inner j before innerOutside
end WNear.Proofs.AllocateRecordCopy

namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 resultMemory finalMemory laidOutMemory

theorem finalMemory_root(p:Layout)(hn:Native p)
    (output:p.out686.toNat+8≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out686.toNat):
    readI32 (finalMemory p) p.allocator.toNat=
      readI32 (AllocateRetry.finalMemory (remainderLayout p)) p.allocator.toNat:=by
  have nums:=stack_numbers p hn
  have native:=copy_native p hn
  have above:=AllocateRetry.result_above_original (remainderLayout p) native.inner.allocation
  have shape:=setup_spec p hn
  have above':p.memory.byteSize≤(result p).toNat:=by
    change (laidOutMemory p).byteSize≤(result p).toNat at above
    rw[shape.2.1] at above
    exact above
  have rootBound:=hn.allocation.allocatorBound
  have heap:=hn.heapAbove
  have lower:=hn.spLower
  apply readI32_congr_bytes
  intro i hi
  have out:p.allocator.toNat+i<p.out686.toNat ∨p.out686.toNat+8≤p.allocator.toNat+i:=by
    rcases output with h|h <;> omega
  have record:=AllocateRecordCopy.resultMemory_allocation_frame (layout690 p) native (p.allocator.toNat+i)
    (by change p.allocator.toNat+i<(result p).toNat;omega)
    (by change p.allocator.toNat+i<p.out.toNat ∨p.out.toNat+8≤p.allocator.toNat+i
        right;rw[nums.2.2.2.2.2.1];omega)
    (by change p.allocator.toNat+i<(reservedSP p+8).toNat ∨(reservedSP p+8).toNat+8≤p.allocator.toNat+i
        right;rw[nums.2.2.2.2.2.2];omega)
  rw[(finalMemory_spec p hn).2.2.2.2.2 (p.allocator.toNat+i) out]
  unfold resultMemory remainderLayout
  exact record
end WNear.Proofs.AllocateVector

namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 finalMemory

theorem finalMemory_root(p:Layout)(hn:Native p)
    (innerOutput:p.out686.toNat+8≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out686.toNat)
    (output:p.out687.toNat+12≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out687.toNat):
    readI32 (finalMemory p) p.allocator.toNat=
      readI32 (AllocateRetry.finalMemory (AllocateVector.remainderLayout p.toVector)) p.allocator.toNat:=by
  have child:=hn.vector p
  have shape:=AllocateVector.finalMemory_spec p.toVector child
  have span:=AllocateVector.resultMemory_spec p.toVector child
  have hb:p.out687.toNat+12≤(allocatedMemory p).byteSize:=by
    change p.out687.toNat+12≤(AllocateVector.finalMemory p.toVector).byteSize
    rw[shape.2.1]
    exact hn.outputBound.trans span.2.1
  have copy:=outputMemory_spec (allocatedMemory p) p.out687 p.size (cacheWord p) shape.1 hb
  apply Eq.trans (b:=readI32 (allocatedMemory p) p.allocator.toNat) _
    (AllocateVector.finalMemory_root p.toVector child innerOutput)
  apply readI32_congr_bytes
  intro i hi
  unfold finalMemory
  apply copy.2.2.2.2.2
  rcases output with h|h <;> omega
end WNear.Proofs.AllocateVectorOuter
