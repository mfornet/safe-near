import Proofs.StorePair
import NearVM.MeteredScalarRules

/-! Byte-level readback of the two-word helper's actual memory result. No
source/destination disjointness is needed for either scratch-word read. -/
namespace WNear.Proofs.StorePairReadback
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.StorePair

/-- Eight little-endian bytes encode exactly the original UInt64. -/
theorem decode_word (value : UInt64) :
    Memory.decodeLE ((List.range 8).map
      (fun i => UInt8.ofNat (value.toNat >>> (8 * i)))) = value.toNat := by
  have hv := value.toNat_lt
  simp [Memory.decodeLE, List.range_succ, Nat.shiftRight_eq_div_pow]
  omega

/-- Reading a word depends only on its eight bytes. -/
theorem readI64_of_bytes (memory : Memory) (address : Nat) (value : UInt64)
    (hbytes : ∀ i, i < 8 → memory.read8 (address + i) =
      UInt8.ofNat (value.toNat >>> (8 * i))) :
    readI64 memory address = value := by
  have hm : (List.range 8).map (fun i => memory.read8 (address + i)) =
      (List.range 8).map (fun i => UInt8.ofNat (value.toNat >>> (8 * i))) := by
    apply List.map_congr_left
    intro i hi
    exact hbytes i (List.mem_range.mp hi)
  have hd := congrArg Memory.decodeLE hm
  rw [decode_word] at hd
  have hread : readI64 memory address = UInt64.ofNat
      (Memory.decodeLE ((List.range 8).map (fun i => memory.read8 (address + i)))) := by
    simp [readI64, Memory.decodeLE, List.foldr_map]
  rw [hread, hd, UInt64.ofNat_toNat]

/-- The low word survives the complete actual two-store sequence. -/
theorem pairMemory_read_low (memory : Memory) (address : Nat) (lo hi : UInt64)
    (hwf : memory.wf) (hbound : address + 16 ≤ memory.byteSize) :
    readI64 (pairMemory memory address lo hi) address = lo := by
  have hs := pairMemory_spec memory address lo hi hwf hbound
  apply readI64_of_bytes
  intro i hi
  rw [hs.2.2.2 (address + i)]
  have hr : address ≤ address + i ∧ address + i < address + 8 := by omega
  simp [hr]

/-- The high word is disjoint from the low word written second. -/
theorem pairMemory_read_high (memory : Memory) (address : Nat) (lo hi : UInt64)
    (hwf : memory.wf) (hbound : address + 16 ≤ memory.byteSize) :
    readI64 (pairMemory memory address lo hi) (address + 8) = hi := by
  have hs := pairMemory_spec memory address lo hi hwf hbound
  apply readI64_of_bytes
  intro i hi
  rw [hs.2.2.2 (address + 8 + i)]
  have hlow : ¬(address ≤ address + 8 + i ∧ address + 8 + i < address + 8) := by omega
  have hhigh : address + 8 ≤ address + 8 + i ∧ address + 8 + i < address + 16 := by omega
  simp [hlow, hhigh]

end WNear.Proofs.StorePairReadback
