import Proofs.StateDispatchLengthMemory
import NearVM.MemoryListWordRules

/-! A separated register-id word survives the actual nested borrow writes. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 readI64
set_option maxRecDepth 16384

private theorem readI64_writeI32_away (memory : Memory) (writeAddress readAddress : Nat) (value : UInt32)
    (hw : memory.wf) (hb : writeAddress + 4 ≤ memory.byteSize)
    (hs : readAddress + 8 ≤ writeAddress ∨ writeAddress + 4 ≤ readAddress) :
    readI64 (writeI32 memory writeAddress value) readAddress = readI64 memory readAddress := by
  have h := writeI32_spec memory writeAddress value hw hb
  apply readI64_congr_bytes
  intro i hi
  have hn : ¬ (writeAddress ≤ readAddress + i ∧ readAddress + i < writeAddress + 4) := by
    rcases hs with hs | hs <;> omega
  rw [h.2.2.2,ite_eq_right hn]

theorem lowMemory_register_frame (p : Layout) (hw : p.memory.wf)
    (hc : 1074904 + 4 ≤ p.memory.byteSize) (hs : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (counterSep : p.input.toNat + 8 ≤ 1074904 ∨ 1074908 ≤ p.input.toNat)
    (scratchSep : p.input.toNat + 8 ≤ (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ p.input.toNat) :
    readI64 (lowMemory p) p.input.toNat = readI64 p.memory p.input.toNat := by
  have b0 : (scratch p).toNat + 4 ≤ p.memory.byteSize := by omega
  have b4 : (scratch p).toNat + 4 + 4 ≤ p.memory.byteSize := by omega
  have b8 : (scratch p).toNat + 8 + 4 ≤ p.memory.byteSize := by omega
  have b12 : (scratch p).toNat + 12 + 4 ≤ p.memory.byteSize := by omega
  have sep0 : p.input.toNat + 8 ≤ (scratch p).toNat ∨ (scratch p).toNat + 4 ≤ p.input.toNat := by
    rcases scratchSep with h | h <;> omega
  have sep4 : p.input.toNat + 8 ≤ (scratch p).toNat + 4 ∨ (scratch p).toNat + 4 + 4 ≤ p.input.toNat := by
    rcases scratchSep with h | h <;> omega
  have sep8 : p.input.toNat + 8 ≤ (scratch p).toNat + 8 ∨ (scratch p).toNat + 8 + 4 ≤ p.input.toNat := by
    rcases scratchSep with h | h <;> omega
  have sep12 : p.input.toNat + 8 ≤ (scratch p).toNat + 12 ∨ (scratch p).toNat + 12 + 4 ≤ p.input.toNat := by
    rcases scratchSep with h | h <;> omega
  let m1 := writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904)
  let m2 := writeI32 m1 ((scratch p).toNat + 4) 1074904
  let m3 := writeI32 m2 (scratch p).toNat 1074908
  let m4 := writeI32 m3 ((scratch p).toNat + 12) (readI32 m3 ((scratch p).toNat + 4))
  let m5 := writeI32 m4 ((scratch p).toNat + 8) (readI32 m4 (scratch p).toNat)
  have s1 := writeI32_spec p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904) hw hc
  have s2 := writeI32_spec m1 ((scratch p).toNat + 4) 1074904 s1.1 (by rw [show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b4)
  have s3 := writeI32_spec m2 (scratch p).toNat 1074908 s2.1 (by rw [show m2.byteSize = m1.byteSize from s2.2.1,show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b0)
  have s4 := writeI32_spec m3 ((scratch p).toNat + 12) (readI32 m3 ((scratch p).toNat + 4)) s3.1
    (by rw [show m3.byteSize = m2.byteSize from s3.2.1,show m2.byteSize = m1.byteSize from s2.2.1,show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b12)
  have r1 := readI64_writeI32_away p.memory 1074904 p.input.toNat (ValueReturnAcquire.nextCount p.memory 1074904) hw hc counterSep
  have r2 := readI64_writeI32_away m1 ((scratch p).toNat + 4) p.input.toNat 1074904 s1.1
    (by rw [show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b4) sep4
  have r3 := readI64_writeI32_away m2 (scratch p).toNat p.input.toNat 1074908 s2.1
    (by rw [show m2.byteSize = m1.byteSize from s2.2.1,show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b0) sep0
  have r4 := readI64_writeI32_away m3 ((scratch p).toNat + 12) p.input.toNat (readI32 m3 ((scratch p).toNat + 4)) s3.1
    (by rw [show m3.byteSize = m2.byteSize from s3.2.1,show m2.byteSize = m1.byteSize from s2.2.1,show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b12) sep12
  have r5 := readI64_writeI32_away m4 ((scratch p).toNat + 8) p.input.toNat (readI32 m4 (scratch p).toNat) s4.1
    (by rw [show m4.byteSize = m3.byteSize from s4.2.1,show m3.byteSize = m2.byteSize from s3.2.1,show m2.byteSize = m1.byteSize from s2.2.1,show m1.byteSize = p.memory.byteSize from s1.2.1]; exact b8) sep8
  have result : readI64 m5 p.input.toNat = readI64 p.memory p.input.toNat := r5.trans (r4.trans (r3.trans (r2.trans r1)))
  simpa only [m5,m4,m3,m2,m1,lowMemory,borrowed,highMemory,acquiredMemory,ValueReturnAcquire.recordMemory,show (1074904 : UInt32) + 4 = 1074908 by decide] using result

end WNear.Proofs.StateDispatchLength
