import Proofs.AllocateRecordCopySteps
import Proofs.PanicAllocateReadback

/-! Exact readbacks of690's two sequential word copies. The high load occurs
in firstMemory; only an explicit separation lemma replaces it by the old word. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem firstMemory_spec (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+4≤memory.byteSize) :
    (firstMemory memory out source).wf ∧
    (firstMemory memory out source).byteSize=memory.byteSize ∧
    (firstMemory memory out source).max=memory.max ∧
    readI32 (firstMemory memory out source) out.toNat=readI32 memory (source.toNat+8) := by
  have spec := writeI32_spec memory out.toNat (readI32 memory (source.toNat+8)) hw hb
  exact ⟨spec.1,spec.2.1,spec.2.2.1,
    PanicAllocateReadback.read_write_self memory out.toNat _ hw hb⟩

theorem finalMemory_shape (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    (finalMemory memory out source).wf ∧
    (finalMemory memory out source).byteSize=memory.byteSize ∧
    (finalMemory memory out source).max=memory.max := by
  have first := firstMemory_spec memory out source hw (by omega)
  have second := writeI32_spec (firstMemory memory out source) (out.toNat+4)
    (readI32 (firstMemory memory out source) (source.toNat+12)) first.1 (by rw [first.2.1];omega)
  exact ⟨second.1,second.2.1.trans first.2.1,second.2.2.1.trans first.2.2.1⟩

/-- Adjacent high-word writing cannot overwrite the first result word, even
when either source interval overlaps either output interval. -/
theorem finalMemory_read_low (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    readI32 (finalMemory memory out source) out.toNat=readI32 memory (source.toNat+8) := by
  have first := firstMemory_spec memory out source hw (by omega)
  have frame := PanicAllocateReadback.read_write_frame (firstMemory memory out source)
    out.toNat (out.toNat+4) (readI32 (firstMemory memory out source) (source.toNat+12))
    first.1 (by rw [first.2.1];omega) (by omega)
  exact frame.trans first.2.2.2

/-- The actual high result is read after the first output write. -/
theorem finalMemory_read_high (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    readI32 (finalMemory memory out source) (out.toNat+4)=
      readI32 (firstMemory memory out source) (source.toNat+12) := by
  have first := firstMemory_spec memory out source hw (by omega)
  exact PanicAllocateReadback.read_write_self (firstMemory memory out source) (out.toNat+4) _
    first.1 (by rw [first.2.1];omega)

/-- Only the first output's four bytes must avoid the high source's four bytes;
no whole-record separation is needed for the original high-word corollary. -/
theorem finalMemory_read_high_original (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (hsep : out.toNat+4≤source.toNat+12 ∨ source.toNat+16≤out.toNat) :
    readI32 (finalMemory memory out source) (out.toNat+4)=readI32 memory (source.toNat+12) := by
  rw [finalMemory_read_high memory out source hw hb]
  exact PanicAllocateReadback.read_write_frame memory (source.toNat+12) out.toNat
    (readI32 memory (source.toNat+8)) hw (by omega) (by omega)

/-- Every byte outside the eight-byte output interval is unchanged. -/
theorem finalMemory_outside (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize)
    (address : Nat) (hout : address<out.toNat ∨ out.toNat+8≤address) :
    (finalMemory memory out source).read8 address=memory.read8 address := by
  have first := writeI32_spec memory out.toNat (readI32 memory (source.toNat+8)) hw (by omega)
  have second := writeI32_spec (firstMemory memory out source) (out.toNat+4)
    (readI32 (firstMemory memory out source) (source.toNat+12)) first.1 (by rw [firstMemory,first.2.1];omega)
  rw [show (finalMemory memory out source).read8 address=_ from second.2.2.2 address]
  rw [ite_eq_right (show ¬(out.toNat+4≤address ∧ address<out.toNat+4+4) by omega)]
  rw [show (firstMemory memory out source).read8 address=_ from first.2.2.2 address]
  rw [ite_eq_right (show ¬(out.toNat≤address ∧ address<out.toNat+4) by omega)]

/-- Complete alias-aware result: both output words, shape, and outside frame. -/
theorem finalMemory_spec (memory : Memory) (out source : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    (finalMemory memory out source).wf ∧
    (finalMemory memory out source).byteSize=memory.byteSize ∧
    (finalMemory memory out source).max=memory.max ∧
    readI32 (finalMemory memory out source) out.toNat=readI32 memory (source.toNat+8) ∧
    readI32 (finalMemory memory out source) (out.toNat+4)=readI32 (firstMemory memory out source) (source.toNat+12) ∧
    ∀ address, (address<out.toNat ∨ out.toNat+8≤address) →
      (finalMemory memory out source).read8 address=memory.read8 address := by
  have shape := finalMemory_shape memory out source hw hb
  exact ⟨shape.1,shape.2.1,shape.2.2,finalMemory_read_low memory out source hw hb,
    finalMemory_read_high memory out source hw hb,finalMemory_outside memory out source hw hb⟩
end WNear.Proofs.AllocateRecordCopy
