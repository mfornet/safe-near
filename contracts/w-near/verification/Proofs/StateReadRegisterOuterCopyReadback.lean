import Proofs.StateReadRegisterOuterCopy
import Proofs.PanicAllocateReadback
import Proofs.StorePairReadback
import NearVM.MemoryListWordRules

/-! The523 result copy keeps exact sequential alias semantics. Only the optional
original-low-word corollary requires separation from the first four-byte write. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] firstMemory finalMemory readI32 readI64 writeI32 writeI64

theorem firstMemory_spec (memory : Memory) (out scratch : UInt32)
    (hw : memory.wf) (hb : (out+8).toNat+4≤memory.byteSize) :
    (firstMemory memory out scratch).wf ∧ (firstMemory memory out scratch).byteSize=memory.byteSize ∧
    (firstMemory memory out scratch).max=memory.max := by
  have h := writeI32_spec memory (out+8).toNat (readI32 memory (scratch+32+8).toNat) hw hb
  simpa only [firstMemory] using And.intro h.1 (And.intro h.2.1 h.2.2.1)

theorem finalMemory_shape (memory : Memory) (out scratch : UInt32)
    (hw : memory.wf) (hh : (out+8).toNat+4≤memory.byteSize) (hl : out.toNat+8≤memory.byteSize) :
    (finalMemory memory out scratch).wf ∧ (finalMemory memory out scratch).byteSize=memory.byteSize ∧
    (finalMemory memory out scratch).max=memory.max := by
  have first := firstMemory_spec memory out scratch hw hh
  have hb : out.toNat+8≤(firstMemory memory out scratch).byteSize := by rw [first.2.1];exact hl
  have h := writeI64_spec (firstMemory memory out scratch) out.toNat (readI64 (firstMemory memory out scratch) (scratch.toNat+32)) first.1 hb
  simpa only [finalMemory] using And.intro h.1 (And.intro (h.2.1.trans first.2.1) (h.2.2.1.trans first.2.2))

theorem finalMemory_low (memory : Memory) (out scratch : UInt32)
    (hw : memory.wf) (hh : (out+8).toNat+4≤memory.byteSize) (hl : out.toNat+8≤memory.byteSize) :
    readI64 (finalMemory memory out scratch) out.toNat=
      readI64 (firstMemory memory out scratch) (scratch.toNat+32) := by
  have first := firstMemory_spec memory out scratch hw hh
  have hb : out.toNat+8≤(firstMemory memory out scratch).byteSize := by rw [first.2.1];exact hl
  have h := writeI64_spec (firstMemory memory out scratch) out.toNat (readI64 (firstMemory memory out scratch) (scratch.toNat+32)) first.1 hb
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [finalMemory,h.2.2.2]
  rw [ite_eq_left (show out.toNat≤out.toNat+i ∧ out.toNat+i<out.toNat+8 by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem finalMemory_high (memory : Memory) (out scratch : UInt32)
    (hw : memory.wf) (hh : (out+8).toNat+4≤memory.byteSize) (hl : out.toNat+8≤memory.byteSize)
    (hn : (out+8).toNat=out.toNat+8) :
    readI32 (finalMemory memory out scratch) (out.toNat+8)=readI32 memory (scratch+32+8).toNat := by
  have first := firstMemory_spec memory out scratch hw hh
  have hb : out.toNat+8≤(firstMemory memory out scratch).byteSize := by rw [first.2.1];exact hl
  have h := writeI64_spec (firstMemory memory out scratch) out.toNat (readI64 (firstMemory memory out scratch) (scratch.toNat+32)) first.1 hb
  have framed : readI32 (finalMemory memory out scratch) (out.toNat+8)=readI32 (firstMemory memory out scratch) (out.toNat+8) := by
    apply LoadedValueReturnData.readI32_frame
    intro i hi
    rw [finalMemory,h.2.2.2,ite_eq_right (show ¬(out.toNat≤out.toNat+8+i ∧ out.toNat+8+i<out.toNat+8) by omega)]
  rw [framed,←hn,firstMemory]
  exact PanicAllocateReadback.read_write_self memory (out+8).toNat (readI32 memory (scratch+32+8).toNat) hw hh

theorem finalMemory_low_original (memory : Memory) (out scratch : UInt32)
    (hw : memory.wf) (hh : (out+8).toNat+4≤memory.byteSize) (hl : out.toNat+8≤memory.byteSize)
    (hs : scratch.toNat+32+8≤(out+8).toNat ∨ (out+8).toNat+4≤scratch.toNat+32) :
    readI64 (finalMemory memory out scratch) out.toNat=readI64 memory (scratch.toNat+32) := by
  rw [finalMemory_low memory out scratch hw hh hl]
  have h := writeI32_spec memory (out+8).toNat (readI32 memory (scratch+32+8).toNat) hw hh
  apply readI64_congr_bytes
  intro i hi
  rw [firstMemory,h.2.2.2,ite_eq_right (show ¬((out+8).toNat≤scratch.toNat+32+i ∧ scratch.toNat+32+i<(out+8).toNat+4) by omega)]

theorem finalMemory_outside (memory : Memory) (out scratch : UInt32)
    (hw : memory.wf) (hh : (out+8).toNat+4≤memory.byteSize) (hl : out.toNat+8≤memory.byteSize)
    (hn : (out+8).toNat=out.toNat+8) (j : Nat) (hj : j<out.toNat ∨ out.toNat+12≤j) :
    (finalMemory memory out scratch).read8 j=memory.read8 j := by
  have first := firstMemory_spec memory out scratch hw hh
  have hb : out.toNat+8≤(firstMemory memory out scratch).byteSize := by rw [first.2.1];exact hl
  have h := writeI64_spec (firstMemory memory out scratch) out.toNat (readI64 (firstMemory memory out scratch) (scratch.toNat+32)) first.1 hb
  have f := writeI32_spec memory (out+8).toNat (readI32 memory (scratch+32+8).toNat) hw hh
  rw [finalMemory,h.2.2.2,ite_eq_right (show ¬(out.toNat≤j ∧ j<out.toNat+8) by omega),
    firstMemory,f.2.2.2,ite_eq_right (show ¬((out+8).toNat≤j ∧ j<(out+8).toNat+4) by omega)]
end WNear.Proofs.StateReadRegisterOuter
