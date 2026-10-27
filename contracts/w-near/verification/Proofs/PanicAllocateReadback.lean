import Proofs.ValueReturnOuterLayout

/-! Native readback of the allocation wrappers' real sequential copies. -/
namespace WNear.Proofs.PanicAllocateReadback
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem read_write_self (memory : Memory) (address : Nat) (value : UInt32)
    (hw : memory.wf) (hb : address + 4 ≤ memory.byteSize) :
    readI32 (writeI32 memory address value) address = value := by
  have spec := writeI32_spec memory address value hw hb
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  rw [spec.2.2.2]
  have inside : address ≤ address + i ∧ address + i < address + 4 := by omega
  rw [ite_eq_left inside]
  simp only [Nat.add_sub_cancel_left]

theorem read_write_frame (memory : Memory) (address target : Nat) (value : UInt32)
    (hw : memory.wf) (hb : target + 4 ≤ memory.byteSize)
    (hs : address + 4 ≤ target ∨ target + 4 ≤ address) :
    readI32 (writeI32 memory target value) address = readI32 memory address := by
  have spec := writeI32_spec memory target value hw hb
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  rw [spec.2.2.2]
  have outside : ¬(target ≤ address + i ∧ address + i < target + 4) := by omega
  rw [ite_eq_right outside]

def lowMemory (memory : Memory) (source target : Nat) := writeI32 memory target (readI32 memory source)
def copyMemory (memory : Memory) (source target : Nat) :=
  writeI32 (lowMemory memory source target) (target + 4) (readI32 (lowMemory memory source target) (source + 4))

/-- The low result word survives the adjacent high write even when source and
output overlap. No separation condition is needed for the returned pointer. -/
theorem copy_low_spec (memory : Memory) (source target : Nat) (alignment : UInt32)
    (hw : memory.wf) (ht : target + 8 ≤ memory.byteSize)
    (hl : readI32 memory source = alignment) :
    (copyMemory memory source target).wf ∧
    (copyMemory memory source target).byteSize = memory.byteSize ∧
    (copyMemory memory source target).max = memory.max ∧
    readI32 (copyMemory memory source target) target = alignment := by
  have hb : target + 4 ≤ memory.byteSize := by omega
  have first := writeI32_spec memory target (readI32 memory source) hw hb
  have hb2 : target + 4 + 4 ≤ (lowMemory memory source target).byteSize := by
    rw [show (lowMemory memory source target).byteSize = memory.byteSize from first.2.1]
    omega
  have second := writeI32_spec (lowMemory memory source target) (target + 4)
    (readI32 (lowMemory memory source target) (source + 4)) first.1 hb2
  have low := read_write_self memory target (readI32 memory source) hw hb
  have frame := read_write_frame (lowMemory memory source target) target (target + 4)
    (readI32 (lowMemory memory source target) (source + 4)) first.1 hb2 (by omega)
  refine ⟨second.1, second.2.1.trans first.2.1, second.2.2.1.trans first.2.2.1, ?_⟩
  change readI32 (writeI32 (lowMemory memory source target) (target + 4) _) target = alignment
  rw [frame, show readI32 (lowMemory memory source target) target = readI32 memory source from low, hl]

/-- The second source load occurs after the first target write. Separation is
needed only for this original-word readback corollary, not the execution rule. -/
theorem copy_spec (memory : Memory) (source target : Nat) (alignment : UInt32)
    (hw : memory.wf) (ht : target + 8 ≤ memory.byteSize)
    (hs : source + 8 ≤ target ∨ target + 8 ≤ source)
    (hl : readI32 memory source = alignment) (hh : readI32 memory (source + 4) = 0) :
    (copyMemory memory source target).wf ∧
    (copyMemory memory source target).byteSize = memory.byteSize ∧
    (copyMemory memory source target).max = memory.max ∧
    readI32 (copyMemory memory source target) target = alignment ∧
    readI32 (copyMemory memory source target) (target + 4) = 0 ∧
    ∀ j, (j < target ∨ target + 8 ≤ j) →
      (copyMemory memory source target).read8 j = memory.read8 j := by
  have hb : target + 4 ≤ memory.byteSize := by omega
  have first := writeI32_spec memory target (readI32 memory source) hw hb
  have hb2 : target + 4 + 4 ≤ (lowMemory memory source target).byteSize := by rw [show (lowMemory memory source target).byteSize = memory.byteSize from first.2.1]; omega
  have second := writeI32_spec (lowMemory memory source target) (target + 4)
    (readI32 (lowMemory memory source target) (source + 4)) first.1 hb2
  have rh : readI32 (lowMemory memory source target) (source + 4) = 0 := by
    have framed := read_write_frame memory (source + 4) target (readI32 memory source) hw hb (by omega)
    change readI32 (writeI32 memory target (readI32 memory source)) (source + 4) = 0
    rw [framed, hh]
  have outLow := read_write_self memory target (readI32 memory source) hw hb
  have frameLow := read_write_frame (lowMemory memory source target) target (target + 4)
    (readI32 (lowMemory memory source target) (source + 4)) first.1 hb2 (by omega)
  have outHigh := read_write_self (lowMemory memory source target) (target + 4)
    (readI32 (lowMemory memory source target) (source + 4)) first.1 hb2
  refine ⟨second.1, second.2.1.trans first.2.1, second.2.2.1.trans first.2.2.1, ?_, ?_, ?_⟩
  · change readI32 (writeI32 (lowMemory memory source target) (target + 4) _) target = alignment
    rw [frameLow, show readI32 (lowMemory memory source target) target = readI32 memory source from outLow, hl]
  · change readI32 (writeI32 (lowMemory memory source target) (target + 4) _) (target + 4) = 0
    rw [outHigh, rh]
  · intro j hj
    change (writeI32 (lowMemory memory source target) (target + 4) _).read8 j = memory.read8 j
    rw [second.2.2.2]
    have n2 : ¬(target + 4 ≤ j ∧ j < target + 4 + 4) := by omega
    rw [ite_eq_right n2]
    change (writeI32 memory target _).read8 j = memory.read8 j
    rw [first.2.2.2]
    have n1 : ¬(target ≤ j ∧ j < target + 4) := by omega
    rw [ite_eq_right n1]

end WNear.Proofs.PanicAllocateReadback
