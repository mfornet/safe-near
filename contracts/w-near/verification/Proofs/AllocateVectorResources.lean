import Proofs.AllocateVectorPhases
import Proofs.AllocateVectorNative
import Proofs.AllocateRecordCopyResult

/-! Original686 native data imply both cached words and the nonzero allocation. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] resultMemory AllocateRecordCopy.resultMemory AllocateRecordCopy.allocatedMemory AllocateRecord.finalMemory AllocateRecord.allocatedMemory derivedGrown targetSaved laidOutMemory

theorem resultMemory_spec (p : Layout) (hn : Native p) :
    (resultMemory p).wf ∧ p.memory.byteSize≤(resultMemory p).byteSize ∧
    (resultMemory p).max=p.memory.max := by
  unfold resultMemory
  have h := AllocateRecordCopy.resultMemory_spec (layout690 p) (copy_native p hn)
  have shape := AllocateRecordCopy.allocated_spec (layout690 p) (copy_native p hn)
  have setup := setup_spec p hn
  refine ⟨h.1,?_,?_⟩
  · rw [h.2.1]
    simpa only [layout690,actualRecord,setup.2.1] using shape.2.1
  · exact h.2.2.trans setup.2.2.1

theorem result_low (p : Layout) (hn : Native p) :
    readI32 (resultMemory p) ((reservedSP p).toNat+8)=result p := by
  have z := AllocateRecordCopy.resultMemory_low (layout690 p) (copy_native p hn)
  have nums := stack_numbers p hn
  have low := hn.spLower
  have addr : (reservedSP p+8).toNat=(reservedSP p).toNat+8 := by
    rw [nums.2.2.2.2.2.2,nums.1];omega
  simpa only [resultMemory,layout690,result,addr] using z

theorem result_high (p : Layout) (hn : Native p) :
    readI32 (resultMemory p) ((reservedSP p).toNat+12)=p.size := by
  have nums := stack_numbers p hn
  have low := hn.spLower
  have sep : (layout690 p).inner.sp.toNat+16≤(layout690 p).out.toNat := by
    simp only [layout690,actualRecord]
    rw [nums.2.1,nums.2.2.2.2.2.2];omega
  have z := AllocateRecordCopy.resultMemory_high_size (layout690 p) (copy_native p hn) (Or.inr sep)
  have addr : (reservedSP p+8).toNat+4=(reservedSP p).toNat+12 := by
    rw [nums.2.2.2.2.2.2,nums.1];omega
  simpa only [resultMemory,layout690,actualRecord,addr] using z

theorem result_nonzero (p : Layout) (hn : Native p) : result p≠0 :=
  AllocateZeroedRetry.result_nonzero (actualRecord p).toZeroed (allocation_native p hn).allocation
end WNear.Proofs.AllocateVector
