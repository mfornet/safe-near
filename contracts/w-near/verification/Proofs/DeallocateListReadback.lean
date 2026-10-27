import Proofs.DeallocateListFrame
import NearVM.MeteredByteMemoryRules
import Init.Data.UInt.Bitwise

/-! Native low-word and byte readback of actual unlinking, with explicit spans. -/
namespace WNear.Proofs.DeallocateListReadback
open Wasm Wasm.Near MeteredLogic DeallocateListState
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem and_assoc32 (a b c : UInt32) : (a &&& b) &&& c = a &&& (b &&& c) := by
  apply UInt32.toBitVec_inj.1
  simp only [UInt32.toBitVec_and, BitVec.and_assoc]

/-- Clearing the allocated bit also clears both low bits when bit two is zero. -/
theorem marked_low_bits (word : UInt32) (h : word &&& 2 = 0) :
    (word &&& 4294967294) &&& 3 = 0 := by
  rw [and_assoc32, show (4294967294 : UInt32) &&& 3 = 2 by decide, h]

/-- Explicit separation keeps the original node word through neighbor writes. -/
theorem second_low (p : Layout) (hw : p.memory.wf)
    (hb1 : (firstLink p).toNat + 8 ≤ p.memory.byteSize)
    (hb2 : (secondLink p).toNat + 4 ≤ (firstMemory p).byteSize)
    (hs1 : p.pointer.toNat + 4 ≤ (firstLink p).toNat + 4 ∨ (firstLink p).toNat + 8 ≤ p.pointer.toNat)
    (hs2 : p.pointer.toNat + 4 ≤ (secondLink p).toNat ∨ (secondLink p).toNat + 4 ≤ p.pointer.toNat) :
    readI32 (secondMemory p) p.pointer.toNat = firstRaw p := by
  have firstSpec := writeI32_spec p.memory ((firstLink p).toNat + 4)
    (DeallocateListWrite.merged p.memory ((firstLink p).toNat + 4) (p.pointer.toNat + 4)) hw (by omega)
  have first := PanicAllocateReadback.read_write_frame p.memory p.pointer.toNat ((firstLink p).toNat + 4)
    (DeallocateListWrite.merged p.memory ((firstLink p).toNat + 4) (p.pointer.toNat + 4)) hw (by omega) (by omega)
  have second := PanicAllocateReadback.read_write_frame (firstMemory p) p.pointer.toNat (secondLink p).toNat
    (DeallocateListWrite.merged (firstMemory p) (secondLink p).toNat p.pointer.toNat) firstSpec.1 hb2 hs2
  exact second.trans first

/-- Native pre-unlink words imply the final cleared byte, rather than a
post-execution flag premise. This is the byte used by f582's actual guard. -/
theorem final_zero_byte (p : Layout) (hw : p.memory.wf)
    (hnode : p.pointer.toNat + 8 ≤ p.memory.byteSize)
    (hb1 : (firstLink p).toNat + 8 ≤ p.memory.byteSize)
    (hb2 : (secondLink p).toNat + 4 ≤ (firstMemory p).byteSize)
    (hs1 : p.pointer.toNat + 4 ≤ (firstLink p).toNat + 4 ∨ (firstLink p).toNat + 8 ≤ p.pointer.toNat)
    (hs2 : p.pointer.toNat + 4 ≤ (secondLink p).toNat ∨ (secondLink p).toNat + 4 ≤ p.pointer.toNat)
    (hz : firstRaw p &&& 3 = 0) :
    readI32 (finalMemory p) p.pointer.toNat = 0 ∧
    readByteWord (finalMemory p) p.pointer.toNat = 0 := by
  have frames := memory_specs p hw hb1 hb2
  have bound : p.pointer.toNat + 8 ≤ (secondMemory p).byteSize := by rw [frames.2.2.2]; exact hnode
  have word := second_low p hw hb1 hb2 hs1 hs2
  have lowzero : readI32 (secondMemory p) p.pointer.toNat &&& 3 = 0 := by rw [word, hz]
  have clear := DeallocateListClear.clear_spec (secondMemory p) p.pointer (finalRaw p) frames.2.2.1 bound
  have low : readI32 (finalMemory p) p.pointer.toNat = 0 := by
    exact clear.2.2.2.1.trans lowzero
  have first := writeI32_spec (secondMemory p) (p.pointer.toNat + 4) (finalRaw p &&& 3) frames.2.2.1 (by omega)
  have highBound : p.pointer.toNat + 4 ≤ (DeallocateListClear.highMemory (secondMemory p) p.pointer (finalRaw p)).byteSize := by
    rw [show (DeallocateListClear.highMemory (secondMemory p) p.pointer (finalRaw p)).byteSize = (secondMemory p).byteSize from first.2.1]; omega
  have middleLow : readI32 (DeallocateListClear.highMemory (secondMemory p) p.pointer (finalRaw p)) p.pointer.toNat =
      readI32 (secondMemory p) p.pointer.toNat :=
    PanicAllocateReadback.read_write_frame (secondMemory p) p.pointer.toNat (p.pointer.toNat + 4)
      (finalRaw p &&& 3) frames.2.2.1 (by omega) (by omega)
  have finalEq : finalMemory p = writeI32 (DeallocateListClear.highMemory (secondMemory p) p.pointer (finalRaw p)) p.pointer.toNat 0 := by
    unfold finalMemory DeallocateListClear.clearMemory
    rw [middleLow, lowzero]
  have last := writeI32_spec (DeallocateListClear.highMemory (secondMemory p) p.pointer (finalRaw p)) p.pointer.toNat 0 first.1 highBound
  refine ⟨low, ?_⟩
  rw [finalEq, readByteWord_eq, last.2.2.2]
  rw [ite_eq_left (show p.pointer.toNat ≤ p.pointer.toNat ∧ p.pointer.toNat < p.pointer.toNat + 4 by omega)]
  simp

end WNear.Proofs.DeallocateListReadback
