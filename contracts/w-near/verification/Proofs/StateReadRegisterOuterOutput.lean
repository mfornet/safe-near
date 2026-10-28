import Proofs.StateReadRegisterOuterReadResult
import Proofs.StateReadRegisterOuterCopyBounds
import Proofs.StateReadRegisterOuterPhases

/-! The final523 result retains its sequential alias semantics. Recovering the
original low eight-byte record needs only separation from the first high write. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 copiedMemory finalMemory readFinalMemory firstMemory

theorem copiedMemory_spec (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    (copiedMemory p).wf ∧ p.memory.byteSize≤(copiedMemory p).byteSize ∧
    (copiedMemory p).max=p.memory.max ∧
    readI64 (copiedMemory p) p.out523.toNat=
      readI64 (firstMemory (readFinalMemory p) p.out523 (scratch p)) ((scratch p).toNat+32) ∧
    readI32 (copiedMemory p) (p.out523.toNat+8)=
      readI32 (readFinalMemory p) (scratch p+32+8).toNat ∧
    ∀ j, (j<p.out523.toNat ∨ p.out523.toNat+12≤j) →
      (copiedMemory p).read8 j=(readFinalMemory p).read8 j := by
  have read := readFinalMemory_spec p hn ha
  have bounds := copy_bounds p hn
  have hh : (p.out523+8).toNat+4≤(readFinalMemory p).byteSize := bounds.2.2.2.1.trans read.2.1
  have hl : p.out523.toNat+8≤(readFinalMemory p).byteSize := bounds.2.2.2.2.2.trans read.2.1
  have shape := finalMemory_shape (readFinalMemory p) p.out523 (scratch p) read.1 hh hl
  unfold copiedMemory
  exact ⟨shape.1,by rw [shape.2.1];exact read.2.1,shape.2.2.trans read.2.2,
    finalMemory_low _ _ _ read.1 hh hl,finalMemory_high _ _ _ read.1 hh hl bounds.1,
    finalMemory_outside _ _ _ read.1 hh hl bounds.1⟩

theorem copiedMemory_low_original (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (hs : (scratch p).toNat+40≤(p.out523+8).toNat ∨ (p.out523+8).toNat+4≤(scratch p).toNat+32) :
    readI64 (copiedMemory p) p.out523.toNat=readI64 (readFinalMemory p) ((scratch p).toNat+32) := by
  have read := readFinalMemory_spec p hn ha
  have bounds := copy_bounds p hn
  unfold copiedMemory
  exact finalMemory_low_original _ _ _ read.1 (bounds.2.2.2.1.trans read.2.1)
    (bounds.2.2.2.2.2.trans read.2.1) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hs)
end WNear.Proofs.StateReadRegisterOuter
