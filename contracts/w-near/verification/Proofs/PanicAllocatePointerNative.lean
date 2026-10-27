import Proofs.PanicAllocatePointerState
import Proofs.PanicAllocateNativeFrame

/-! Native consequences of f503's original stack and memory conditions. -/
namespace WNear.Proofs.PanicAllocatePointerNative
open Wasm Wasm.Near MeteredLogic PanicAllocatePointerState
set_option maxRecDepth 16384

/-- Both nested stack records fit below the original stack pointer. -/
theorem spans (p : Layout) (hsp : 32 ≤ p.sp.toNat) (hb : p.sp.toNat ≤ p.memory.byteSize) :
    (PanicAllocateState.scratch (inner p)).toNat + 16 ≤ p.memory.byteSize ∧
    (inner p).out.toNat + 8 ≤ p.memory.byteSize ∧
    (PanicAllocateState.scratch (inner p)).toNat + 16 ≤ p.sp.toNat ∧
    (inner p).out.toNat + 8 ≤ p.sp.toNat := by
  have lower : 16 ≤ p.sp.toNat := by omega
  have outer := StorePairAddresses.sub_sixteen p.sp lower
  have mid : 16 ≤ (scratch p).toNat := by simpa only [scratch] using (show 16 ≤ (p.sp - 16).toNat by rw [outer]; omega)
  have nested := StorePairAddresses.sub_sixteen (scratch p) mid
  have out := StorePairAddresses.scratch_add_eight p.sp lower
  simp only [inner, PanicAllocateState.scratch]
  change ((scratch p - 16).toNat + 16 ≤ p.memory.byteSize) ∧
    ((scratch p + 8).toNat + 8 ≤ p.memory.byteSize) ∧
    ((scratch p - 16).toNat + 16 ≤ p.sp.toNat) ∧
    ((scratch p + 8).toNat + 8 ≤ p.sp.toNat)
  change (scratch p + 8).toNat = (scratch p).toNat + 8 at out
  rw [nested, out]
  change (p.sp - 16).toNat = p.sp.toNat - 16 at outer
  have he : (scratch p).toNat = p.sp.toNat - 16 := outer
  rw [he]
  omega

/-- The return pointer is one, derived from original native conditions. -/
theorem final_spec (p : Layout) (hw : p.memory.wf) (hwidth : p.memory.byteSize ≤ 2 ^ 32)
    (hsp : 32 ≤ p.sp.toNat) (hb : p.sp.toNat ≤ p.memory.byteSize) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize = p.memory.byteSize ∧
    (finalMemory p).max = p.memory.max ∧ readI32 (finalMemory p) (scratch p + 8).toNat = 1 := by
  have h := spans p hsp hb
  exact PanicAllocateNative.final_spec (inner p) hw hwidth h.1 h.2.1

/-- Panic flags and other words above the initial stack retain their values. -/
theorem final_read_above_stack (p : Layout) (hw : p.memory.wf)
    (hwidth : p.memory.byteSize ≤ 2 ^ 32) (hsp : 32 ≤ p.sp.toNat)
    (hb : p.sp.toNat ≤ p.memory.byteSize) (address : Nat) (ha : p.sp.toNat ≤ address) :
    readI32 (finalMemory p) address = readI32 p.memory address := by
  have h := spans p hsp hb
  exact PanicAllocateNativeFrame.final_read_frame (inner p) hw hwidth h.1 h.2.1 address
    (Or.inr (by have bound := h.2.2.1; omega)) (Or.inr (by have bound := h.2.2.2; omega))

end WNear.Proofs.PanicAllocatePointerNative
