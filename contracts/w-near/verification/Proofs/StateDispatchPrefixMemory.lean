import Proofs.StateDispatchPrefixFrame

/-! Sequential acquisition writes preserve the original memory shape. -/
namespace WNear.Proofs.StateDispatchPrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32
theorem acquiredMemory_specs (p : Layout) (hwf : p.memory.wf)
    (hc : 1074904 + 4 ≤ p.memory.byteSize) (ho : (scratch p).toNat + 8 ≤ p.memory.byteSize) :
    (acquiredMemory p).wf ∧ (acquiredMemory p).byteSize = p.memory.byteSize ∧ (acquiredMemory p).max = p.memory.max := by
  have cell := writeI32_spec p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904) hwf hc
  have high := writeI32_spec (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904))
    ((scratch p).toNat + 4) 1074904 cell.1 (by rw [cell.2.1]; omega)
  have low := writeI32_spec (writeI32 (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904))
    ((scratch p).toNat + 4) 1074904) (scratch p).toNat 1074908 high.1 (by rw [high.2.1,cell.2.1]; omega)
  exact ⟨low.1,low.2.1.trans (high.2.1.trans cell.2.1),low.2.2.1.trans (high.2.2.1.trans cell.2.2.1)⟩


end WNear.Proofs.StateDispatchPrefix
