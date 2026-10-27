import Proofs.ValueReturnWrapper
import Proofs.ValueReturnDispatch

/-! The actual wrapper stores establish the pointer/length read by f456. -/
namespace WNear.Proofs.ValueReturnSlice
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.ValueReturnWrapper

/-- Four encoded bytes recover exactly the original u32. -/
theorem decode_word (value : UInt32) :
    Memory.decodeLE ((List.range 4).map
      (fun i => UInt8.ofNat (value.toNat >>> (8 * i)))) = value.toNat := by
  have hv := value.toNat_lt
  simp [Memory.decodeLE, List.range_succ, Nat.shiftRight_eq_div_pow]
  omega

/-- The actual load32_u reads the full original value, zero extended to u64. -/
theorem packed32_of_bytes (memory : Memory) (address : Nat) (value : UInt32)
    (hbytes : ∀ i, i < 4 → memory.read8 (address + i) =
      UInt8.ofNat (value.toNat >>> (8 * i))) :
    ValueReturnDispatch.packed32 memory address = UInt64.ofNat value.toNat := by
  have hm : (List.range 4).map (fun i => memory.read8 (address + i)) =
      (List.range 4).map (fun i => UInt8.ofNat (value.toNat >>> (8 * i))) := by
    apply List.map_congr_left
    intro i hi
    exact hbytes i (List.mem_range.mp hi)
  have hd := congrArg Memory.decodeLE hm
  rw [decode_word] at hd
  have hr : ValueReturnDispatch.packed32 memory address = UInt64.ofNat
      (Memory.decodeLE ((List.range 4).map (fun i => memory.read8 (address + i)))) := by
    simp [ValueReturnDispatch.packed32, Memory.decodeLE, List.foldr_map]
  rw [hr, hd]

/-- Both words and their complete frame follow from the actual sequential
stores. The input pointer may alias the wrapper's scratch memory. -/
theorem sliceMemory_spec (memory : Memory) (scratch pointer length : UInt32)
    (hwf : memory.wf) (hspan : scratch.toNat + 16 ≤ memory.byteSize) :
    (sliceMemory memory scratch pointer length).wf ∧
    (sliceMemory memory scratch pointer length).byteSize = memory.byteSize ∧
    (sliceMemory memory scratch pointer length).max = memory.max ∧
    ValueReturnDispatch.packed32 (sliceMemory memory scratch pointer length) (scratch.toNat + 8) = UInt64.ofNat pointer.toNat ∧
    ValueReturnDispatch.packed32 (sliceMemory memory scratch pointer length) (scratch.toNat + 12) = UInt64.ofNat length.toNat ∧
    ∀ j, (j < scratch.toNat + 8 ∨ scratch.toNat + 16 ≤ j) →
      (sliceMemory memory scratch pointer length).read8 j = memory.read8 j := by
  have first := writeI32_spec memory (scratch.toNat + 12) length hwf (by omega)
  have hbound : scratch.toNat + 8 + 4 ≤ (writeI32 memory (scratch.toNat + 12) length).byteSize := by
    rw [first.2.1]; omega
  have second := writeI32_spec (writeI32 memory (scratch.toNat + 12) length) (scratch.toNat + 8) pointer first.1 hbound
  refine ⟨second.1, second.2.1.trans first.2.1, second.2.2.1.trans first.2.2.1, ?_, ?_, ?_⟩
  · apply packed32_of_bytes
    intro i hi
    rw [sliceMemory, second.2.2.2]
    have hinside : scratch.toNat + 8 ≤ scratch.toNat + 8 + i ∧
        scratch.toNat + 8 + i < scratch.toNat + 8 + 4 := by omega
    simp [hinside]
  · apply packed32_of_bytes
    intro i hi
    rw [sliceMemory, second.2.2.2, first.2.2.2]
    have houtside : ¬ (scratch.toNat + 8 ≤ scratch.toNat + 12 + i ∧
        scratch.toNat + 12 + i < scratch.toNat + 8 + 4) := by omega
    have hinside : scratch.toNat + 12 ≤ scratch.toNat + 12 + i ∧
        scratch.toNat + 12 + i < scratch.toNat + 12 + 4 := by omega
    simp [houtside, hinside]
  · intro j hj
    rw [sliceMemory, second.2.2.2, first.2.2.2]
    have ho : ¬ (scratch.toNat + 8 ≤ j ∧ j < scratch.toNat + 8 + 4) := by omega
    have hl : ¬ (scratch.toNat + 12 ≤ j ∧ j < scratch.toNat + 12 + 4) := by omega
    simp [ho, hl]

end WNear.Proofs.ValueReturnSlice
