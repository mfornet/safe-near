import NearVM.MemoryListRules
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredScalarRules

/-! Packed word reads are preserved outside a bounded whole-register copy. -/
namespace Wasm.Near.MeteredLogic

theorem readI32_congr_bytes (before after : Memory) (address : Nat)
    (h : ∀ i < 4, after.read8 (address + i) = before.read8 (address + i)) :
    readI32 after address = readI32 before address := by
  let decode := fun bytes : List UInt8 => UInt32.ofNat (bytes.foldr (fun byte acc => acc * 256 + byte.toNat) 0)
  change decode ((List.range 4).map (fun i => after.read8 (address + i))) =
    decode ((List.range 4).map (fun i => before.read8 (address + i)))
  apply congrArg decode
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem readI64_congr_bytes (before after : Memory) (address : Nat)
    (h : ∀ i < 8, after.read8 (address + i) = before.read8 (address + i)) :
    readI64 after address = readI64 before address := by
  let decode := fun bytes : List UInt8 => UInt64.ofNat (bytes.foldr (fun byte acc => acc * 256 + byte.toNat) 0)
  change decode ((List.range 8).map (fun i => after.read8 (address + i))) =
    decode ((List.range 8).map (fun i => before.read8 (address + i)))
  apply congrArg decode
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem readI32_writeList_away (memory : Memory) (address readAddress : Nat) (bytes : List UInt8)
    (hw : memory.wf) (hb : address + bytes.length ≤ memory.byteSize)
    (hs : readAddress + 4 ≤ address ∨ address + bytes.length ≤ readAddress) :
    readI32 (memory.writeList address bytes) readAddress = readI32 memory readAddress := by
  have h := memory.writeList_spec bytes address hw hb
  apply readI32_congr_bytes
  intro i hi
  have hn : ¬ (address ≤ readAddress + i ∧ readAddress + i < address + bytes.length) := by
    rcases hs with hs | hs <;> omega
  rw [h.2.2.2,ite_eq_right hn]

theorem readI64_writeList_away (memory : Memory) (address readAddress : Nat) (bytes : List UInt8)
    (hw : memory.wf) (hb : address + bytes.length ≤ memory.byteSize)
    (hs : readAddress + 8 ≤ address ∨ address + bytes.length ≤ readAddress) :
    readI64 (memory.writeList address bytes) readAddress = readI64 memory readAddress := by
  have h := memory.writeList_spec bytes address hw hb
  apply readI64_congr_bytes
  intro i hi
  have hn : ¬ (address ≤ readAddress + i ∧ readAddress + i < address + bytes.length) := by
    rcases hs with hs | hs <;> omega
  rw [h.2.2.2,ite_eq_right hn]

end Wasm.Near.MeteredLogic
