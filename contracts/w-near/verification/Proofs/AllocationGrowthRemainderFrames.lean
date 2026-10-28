import Proofs.AllocationGrowthRemainderFinal
import Proofs.AllocateRecordOldFrame
import Proofs.AllocateVectorOuterOldFrame

/-! New-page remainder bytes before the allocated payload survive zero filling
and both allocation-result wrappers. Output bounds refer to original memory. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 finalMemory

theorem finalMemory_before_payload (p:Layout)(hn:Native p)(j:Nat)
    (before:j<(result p).toNat):
    (finalMemory p).read8 j=(AllocateRetry.finalMemory p.toRetry).read8 j:=by
  rw[(finalMemory_spec p hn).2.2.2 j,ite_eq_right (by omega)]
  rfl
end WNear.Proofs.AllocateZeroedRetry

namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem finalMemory_new_remainder(p:Layout)(hn:Native p)(j:Nat)
    (above:p.memory.byteSize≤j)(before:j<(result p).toNat):
    (finalMemory p).read8 j=(AllocateRetry.finalMemory p.toZeroed.toRetry).read8 j:=by
  have bound:=hn.outputBound
  rw[(finalMemory_spec p hn).2.2.2.2.2 j (Or.inr (by omega))]
  exact AllocateZeroedRetry.finalMemory_before_payload p.toZeroed hn.allocation j before
end WNear.Proofs.AllocateRecord

namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem resultMemory_new_remainder(p:Layout)(hn:Native p)(j:Nat)
    (above:p.inner.memory.byteSize≤j)(before:j<(AllocateRecord.result p.inner).toNat):
    (resultMemory p).read8 j=(AllocateRetry.finalMemory p.inner.toZeroed.toRetry).read8 j:=by
  have a:=AllocateRecord.finalMemory_spec p.inner hn.inner
  have b:=AllocateRecord.allocated_spec p.inner hn.inner
  have hb:p.out.toNat+8≤(allocatedMemory p).byteSize:=by
    change p.out.toNat+8≤(AllocateRecord.finalMemory p.inner).byteSize
    rw[a.2.1]
    have bound:=hn.outputBound
    omega
  have outside:j<p.out.toNat ∨p.out.toNat+8≤j:=by
    right;have h:=hn.outputBound;omega
  rw[show resultMemory p=finalMemory (allocatedMemory p) p.out p.inner.sp from rfl,
    finalMemory_outside (allocatedMemory p) p.out p.inner.sp a.1 hb j outside]
  exact AllocateRecord.finalMemory_new_remainder p.inner hn.inner j above before
end WNear.Proofs.AllocateRecordCopy

namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 resultMemory finalMemory laidOutMemory

def remainderLayout(p:Layout):AllocateRetry.Layout:=(layout690 p).inner.toZeroed.toRetry

theorem finalMemory_new_remainder(p:Layout)(hn:Native p)(j:Nat)
    (above:p.memory.byteSize≤j)(before:j<(result p).toNat):
    (finalMemory p).read8 j=(AllocateRetry.finalMemory (remainderLayout p)).read8 j:=by
  have setup:=setup_spec p hn
  have nums:=stack_numbers p hn
  have bound:=hn.outputBound
  rw[(finalMemory_spec p hn).2.2.2.2.2 j (Or.inr (by omega))]
  have child:=AllocateRecordCopy.resultMemory_new_remainder (layout690 p) (copy_native p hn) j
    (by change (laidOutMemory p).byteSize≤j;rw[setup.2.1];exact above) before
  unfold resultMemory remainderLayout
  exact child
end WNear.Proofs.AllocateVector

namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 finalMemory

theorem finalMemory_new_remainder(p:Layout)(hn:Native p)(j:Nat)
    (above:p.memory.byteSize≤j)(before:j<(AllocateVector.result p.toVector).toNat):
    (finalMemory p).read8 j=(AllocateRetry.finalMemory (AllocateVector.remainderLayout p.toVector)).read8 j:=by
  have child:=hn.vector p
  have shape:=AllocateVector.finalMemory_spec p.toVector child
  have span:=AllocateVector.resultMemory_spec p.toVector child
  have hb:p.out687.toNat+12≤(allocatedMemory p).byteSize:=by
    change p.out687.toNat+12≤(AllocateVector.finalMemory p.toVector).byteSize
    rw[shape.2.1]
    exact hn.outputBound.trans span.2.1
  have out:p.out687.toNat+12≤p.memory.byteSize:=hn.outputBound
  have copy:=outputMemory_spec (allocatedMemory p) p.out687 p.size (cacheWord p) shape.1 hb
  unfold finalMemory
  rw[copy.2.2.2.2.2 j (Or.inr (by omega))]
  exact AllocateVector.finalMemory_new_remainder p.toVector child j above before
end WNear.Proofs.AllocateVectorOuter
