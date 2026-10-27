import Proofs.PanicAllocateState
import Proofs.PanicAllocateReadback

/-! Native readback for the actual zero-size wrapper, including overlapping spans. -/
namespace WNear.Proofs.PanicAllocateNative
open Wasm Wasm.Near MeteredLogic PanicAllocateState
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

/-- The pointer returned by f503 follows from the actual f508 memory writes.
There is no post-state read assumption or separation requirement. -/
theorem final_spec (p : Layout) (hw : p.memory.wf)
    (hwidth : p.memory.byteSize ≤ 2 ^ 32)
    (hs : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (ho : p.out.toNat + 8 ≤ p.memory.byteSize) :
    (finalMemory p).wf ∧
    (finalMemory p).byteSize = p.memory.byteSize ∧
    (finalMemory p).max = p.memory.max ∧
    readI32 (finalMemory p) p.out.toNat = p.alignment := by
  have haddr : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    rw [UInt32.toNat_add]
    change ((scratch p).toNat + 8) % 2 ^ 32 = (scratch p).toNat + 8
    rw [Nat.mod_eq_of_lt (by omega)]
  have hb : (scratch p + 8).toNat + 8 ≤ p.memory.byteSize := by rw [haddr]; omega
  have initial := PanicAllocateZero.zeroMemory_spec p.memory (scratch p + 8).toNat p.alignment hw hb
  have low : readI32 (allocatedMemory p) ((scratch p).toNat + 8) = p.alignment := by
    simpa only [allocatedMemory, haddr] using initial.2.2.2.1
  have outBound : p.out.toNat + 8 ≤ (allocatedMemory p).byteSize := by
    rw [show (allocatedMemory p).byteSize = p.memory.byteSize from initial.2.1]
    exact ho
  have copied := PanicAllocateReadback.copy_low_spec (allocatedMemory p)
    ((scratch p).toNat + 8) p.out.toNat p.alignment initial.1 outBound low
  have memoryEq : finalMemory p = PanicAllocateReadback.copyMemory (allocatedMemory p)
      ((scratch p).toNat + 8) p.out.toNat := by
    simp only [finalMemory, lowMemory, PanicAllocateReadback.copyMemory, PanicAllocateReadback.lowMemory, Nat.add_assoc]
  rw [memoryEq]
  exact ⟨copied.1, copied.2.1.trans initial.2.1,
    copied.2.2.1.trans initial.2.2.1, copied.2.2.2⟩

end WNear.Proofs.PanicAllocateNative
