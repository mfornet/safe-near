import Proofs.AllocateSplit
import Proofs.PanicAllocateReadback

/-! Original-header readback for the actual sequential end-split initialization. -/
namespace WNear.Proofs.Allocate
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 writeI64

/-- Four equal bytes give equal actual loads, without a spatial assumption. -/
theorem readI32_congr_bytes (first second : Memory) (address : Nat)
    (h : ∀ i, i < 4 → first.read8 (address+i) = second.read8 (address+i)) :
    readI32 first address = readI32 second address := by
  have zero : first.read8 address = second.read8 address := by simpa only [Nat.add_zero] using h 0 (by decide)
  simp [readI32,List.range_succ,h,zero]

/-- In the native split interval, clearing the new header preserves the old end. -/
theorem cleared_read_old (memory : Memory) (head header : UInt32) (hw : memory.wf)
    (hb : header.toNat + 12 ≤ memory.byteSize) (hs : head.toNat + 4 ≤ header.toNat) :
    readI32 (clearedMemory memory header) head.toNat = readI32 memory head.toNat := by
  apply readI32_congr_bytes
  intro i hi
  exact (clearedMemory_spec memory header hw hb).2.2.2 _ (Or.inl (by omega))

/-- This is the memory actually used by initializedStore, including its post-clear read. -/
def initializedMemory (memory : Memory) (head header : UInt32) :=
  writeI32 (clearedMemory memory header) header.toNat
    (readI32 (clearedMemory memory header) head.toNat &&& 4294967292)

theorem initializedMemory_spec (memory : Memory) (head header : UInt32) (hw : memory.wf)
    (hb : header.toNat + 12 ≤ memory.byteSize) (hs : head.toNat + 4 ≤ header.toNat) :
    (initializedMemory memory head header).wf ∧
    (initializedMemory memory head header).byteSize = memory.byteSize ∧
    (initializedMemory memory head header).max = memory.max ∧
    readI32 (initializedMemory memory head header) header.toNat = (readI32 memory head.toNat &&& 4294967292) ∧
    readI32 (initializedMemory memory head header) head.toNat = readI32 memory head.toNat ∧
    ∀ j, j < header.toNat ∨ header.toNat+12 ≤ j →
      (initializedMemory memory head header).read8 j = memory.read8 j := by
  have clear := clearedMemory_spec memory header hw hb
  have cb : header.toNat + 4 ≤ (clearedMemory memory header).byteSize := by rw [clear.2.1]; omega
  have written := writeI32_spec (clearedMemory memory header) header.toNat
    (readI32 (clearedMemory memory header) head.toNat &&& 4294967292) clear.1 cb
  have old := cleared_read_old memory head header hw hb hs
  have self := PanicAllocateReadback.read_write_self (clearedMemory memory header) header.toNat
    (readI32 (clearedMemory memory header) head.toNat &&& 4294967292) clear.1 cb
  have previous := PanicAllocateReadback.read_write_frame (clearedMemory memory header) head.toNat header.toNat
    (readI32 (clearedMemory memory header) head.toNat &&& 4294967292) clear.1 cb (Or.inl hs)
  refine ⟨written.1,written.2.1.trans clear.2.1,written.2.2.1.trans clear.2.2.1,?_,previous.trans old,?_⟩
  · exact self.trans (congrArg (fun v : UInt32 => v &&& 4294967292) old)
  · intro j hj
    rw [show (initializedMemory memory head header).read8 j = _ from written.2.2.2 j]
    rw [ite_eq_right (show ¬(header.toNat ≤ j ∧ j < header.toNat+4) by omega)]
    exact clear.2.2.2 j hj

theorem cleared_high_zero (memory : Memory) (header : UInt32) (hw : memory.wf)
    (hb : header.toNat + 12 ≤ memory.byteSize) :
    readI32 (clearedMemory memory header) (header.toNat+4) = 0 := by
  have first := writeI32_spec memory (header.toNat+8) 0 hw (by omega)
  have bound : header.toNat+8 ≤ (writeI32 memory (header.toNat+8) 0).byteSize := by rw [first.2.1]; omega
  have second := writeI64_spec (writeI32 memory (header.toNat+8) 0) header.toNat 0 first.1 bound
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  rw [show (clearedMemory memory header).read8 (header.toNat+4+i) = _ from second.2.2.2 _]
  rw [ite_eq_left (show header.toNat ≤ header.toNat+4+i ∧ header.toNat+4+i < header.toNat+8 by omega)]
  simp

theorem initialized_high_zero (memory : Memory) (head header : UInt32) (hw : memory.wf)
    (hb : header.toNat+12 ≤ memory.byteSize) :
    readI32 (initializedMemory memory head header) (header.toNat+4) = 0 := by
  have clear := clearedMemory_spec memory header hw hb
  have cb : header.toNat+4 ≤ (clearedMemory memory header).byteSize := by rw [clear.2.1]; omega
  have frame := PanicAllocateReadback.read_write_frame (clearedMemory memory header) (header.toNat+4) header.toNat
    (readI32 (clearedMemory memory header) head.toNat &&& 4294967292) clear.1 cb (Or.inr (by omega))
  exact frame.trans (cleared_high_zero memory header hw hb)

end WNear.Proofs.Allocate
