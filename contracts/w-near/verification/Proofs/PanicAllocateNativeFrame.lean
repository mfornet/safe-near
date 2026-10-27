import Proofs.PanicAllocateNative

/-! Original-memory frames for the zero-size panic allocation wrappers. -/
namespace WNear.Proofs.PanicAllocateNativeFrame
open Wasm Wasm.Near MeteredLogic PanicAllocateState
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem copy_byte_frame (memory : Memory) (source target j : Nat)
    (hw : memory.wf) (ht : target + 8 ≤ memory.byteSize)
    (hj : j < target ∨ target + 8 ≤ j) :
    (PanicAllocateReadback.copyMemory memory source target).read8 j = memory.read8 j := by
  have hb : target + 4 ≤ memory.byteSize := by omega
  have first := writeI32_spec memory target (readI32 memory source) hw hb
  have hb2 : target + 4 + 4 ≤ (PanicAllocateReadback.lowMemory memory source target).byteSize := by
    rw [show (PanicAllocateReadback.lowMemory memory source target).byteSize = memory.byteSize from first.2.1]
    omega
  have second := writeI32_spec (PanicAllocateReadback.lowMemory memory source target) (target + 4)
    (readI32 (PanicAllocateReadback.lowMemory memory source target) (source + 4)) first.1 hb2
  change (writeI32 (PanicAllocateReadback.lowMemory memory source target) (target + 4) _).read8 j = memory.read8 j
  rw [second.2.2.2, ite_eq_right (show ¬(target + 4 ≤ j ∧ j < target + 4 + 4) by omega)]
  change (writeI32 memory target _).read8 j = memory.read8 j
  rw [first.2.2.2, ite_eq_right (show ¬(target ≤ j ∧ j < target + 4) by omega)]

/-- Every byte outside the native scratch and result spans is preserved. -/
theorem final_byte_frame (p : Layout) (hw : p.memory.wf)
    (hwidth : p.memory.byteSize ≤ 2 ^ 32)
    (hs : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (ho : p.out.toNat + 8 ≤ p.memory.byteSize)
    (j : Nat) (hjs : j < (scratch p).toNat + 8 ∨ (scratch p).toNat + 16 ≤ j)
    (hjo : j < p.out.toNat ∨ p.out.toNat + 8 ≤ j) :
    (finalMemory p).read8 j = p.memory.read8 j := by
  have haddr : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    rw [UInt32.toNat_add]
    change ((scratch p).toNat + 8) % 2 ^ 32 = (scratch p).toNat + 8
    rw [Nat.mod_eq_of_lt (by omega)]
  have hb : (scratch p + 8).toNat + 8 ≤ p.memory.byteSize := by rw [haddr]; omega
  have initial := PanicAllocateZero.zeroMemory_spec p.memory (scratch p + 8).toNat p.alignment hw hb
  have outBound : p.out.toNat + 8 ≤ (allocatedMemory p).byteSize := by
    rw [show (allocatedMemory p).byteSize = p.memory.byteSize from initial.2.1]
    exact ho
  have copied := copy_byte_frame (allocatedMemory p) ((scratch p).toNat + 8) p.out.toNat j initial.1 outBound hjo
  have memoryEq : finalMemory p = PanicAllocateReadback.copyMemory (allocatedMemory p)
      ((scratch p).toNat + 8) p.out.toNat := by
    simp only [finalMemory, lowMemory, PanicAllocateReadback.copyMemory, PanicAllocateReadback.lowMemory, Nat.add_assoc]
  rw [memoryEq, copied]
  exact initial.2.2.2.2.2 j (by simpa only [haddr, Nat.add_assoc] using hjs)

/-- Static words outside the two written records retain their initial value. -/
theorem final_read_frame (p : Layout) (hw : p.memory.wf)
    (hwidth : p.memory.byteSize ≤ 2 ^ 32)
    (hs : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (ho : p.out.toNat + 8 ≤ p.memory.byteSize) (address : Nat)
    (has : address + 4 ≤ (scratch p).toNat + 8 ∨ (scratch p).toNat + 16 ≤ address)
    (hao : address + 4 ≤ p.out.toNat ∨ p.out.toNat + 8 ≤ address) :
    readI32 (finalMemory p) address = readI32 p.memory address := by
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  exact final_byte_frame p hw hwidth hs ho (address + i) (by omega) (by omega)

end WNear.Proofs.PanicAllocateNativeFrame
