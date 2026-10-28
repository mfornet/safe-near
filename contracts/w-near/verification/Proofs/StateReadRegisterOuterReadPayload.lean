import Proofs.StateReadRegisterOuterReadStatic
import Proofs.AllocateRetryOldFrame
import Proofs.AllocateVectorOuterRecordReadback

/-! The actual allocation pointer and requested payload span follow from the
original growth/retry domain and all subsequent memory extents. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] actualRecord laidOutMemory derivedGrown targetSaved layout690 result AllocateRetry.finalMemory AllocateRetry.growthLayout AllocateGrowth.delta resultMemory finalMemory AllocateRecord.finalMemory AllocateRecord.allocatedMemory AllocateRecordCopy.resultMemory AllocateRecordCopy.allocatedMemory AllocateZeroedRetry.finalMemory

theorem result_payload (p : Layout) (hn : Native p) :
    p.memory.byteSize≤(result p).toNat ∧ (result p).toNat+p.size.toNat≤(finalMemory p).byteSize := by
  have native := allocation_native p hn
  have retry := native.allocation
  have span := AllocateRetry.result_size_span (actualRecord p).toRetry retry
  have above := AllocateRetry.result_above_original (actualRecord p).toRetry retry
  have rs := AllocateRetry.finalMemory_spec (actualRecord p).toRetry retry
  have zs := AllocateZeroedRetry.finalMemory_spec (actualRecord p).toZeroed retry
  have record := AllocateRecord.finalMemory_spec (actualRecord p) native
  have copy := AllocateRecordCopy.resultMemory_spec (layout690 p) (copy_native p hn)
  have fin := finalMemory_spec p hn
  have setup := setup_spec p hn
  have outSize : (finalMemory p).byteSize=(AllocateRetry.finalMemory (actualRecord p).toRetry).byteSize := by
    rw [fin.2.1]
    have copySize : (resultMemory p).byteSize=(AllocateRecord.finalMemory (actualRecord p)).byteSize := by
      simpa only [resultMemory,AllocateRecordCopy.allocatedMemory,layout690] using copy.2.1
    rw [copySize,record.2.1]
    have zeroSize : (AllocateRecord.allocatedMemory (actualRecord p)).byteSize=(AllocateRetry.finalMemory (actualRecord p).toRetry).byteSize := by
      simpa only [AllocateRecord.allocatedMemory,rs.2.1] using zs.2.1
    exact zeroSize
  have oldSize : (actualRecord p).memory.byteSize=p.memory.byteSize := by
    simpa only [actualRecord] using setup.2.1
  have sameSize : (actualRecord p).size=p.size := by simp only [actualRecord]
  have sameResult : AllocateRetry.result (actualRecord p).toRetry=result p := by
    unfold result AllocateRecord.result AllocateZeroedRetry.result
    rfl
  rw [oldSize,sameResult] at above
  rw [sameResult,sameSize,←outSize] at span
  exact ⟨above,span⟩
end WNear.Proofs.AllocateVector

namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] finalMemory allocatedMemory cacheWord

theorem result_payload (p : Layout) (hn : Native p) :
    p.memory.byteSize≤(AllocateVector.result p.toVector).toNat ∧
    (AllocateVector.result p.toVector).toNat+p.size.toNat≤(finalMemory p).byteSize := by
  have native := hn.vector p
  have payload := AllocateVector.result_payload p.toVector native
  have shape := allocated_spec p hn
  have output := outputMemory_spec (allocatedMemory p) p.out687 p.size (cacheWord p) shape.1
    (hn.outputBound.trans shape.2.1)
  have finalSize : (finalMemory p).byteSize=(AllocateVector.finalMemory p.toVector).byteSize := by
    simpa only [finalMemory,allocatedMemory] using output.2.1
  rw [finalSize]
  exact payload
end WNear.Proofs.AllocateVectorOuter
