import Proofs.StateReadStorageOuterResultReady

/-! The complete f548 result copy has its actual sequential alias semantics. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] registeredMemory finalMemory readI32 readI64

theorem finalMemory_shape (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=(registeredMemory p).byteSize ∧
    (finalMemory p).max=(registeredMemory p).max := by
  have b := result_bounds p hn ha
  have shape := StateReadResult.finalMemory_spec (registeredMemory p) p.out548 (scratch p+16)
    b.1 b.2.1 b.2.2.2.1
  unfold finalMemory
  exact ⟨shape.1,shape.2.1,shape.2.2.1⟩

/-- Pointer and capacity retain the original packed snapshot for every output alias. -/
theorem finalMemory_low_record (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    readI32 (finalMemory p) p.out548.toNat=
      AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector ∧
    readI32 (finalMemory p) (p.out548.toNat+4)=p.size := by
  have b := result_bounds p hn ha
  have words := StateReadResult.finalMemory_low_words (registeredMemory p) p.out548 (scratch p+16)
    b.1 b.2.1 b.2.2.2.1 b.2.2.2.2.2.1
  have record := registeredMemory_record p hn ha
  unfold finalMemory
  exact ⟨words.1.trans record.1,words.2.trans record.2.1⟩

/-- Only the actual eight-byte write versus four-byte source read needs separation. -/
theorem finalMemory_length (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (hs : (scratch p+16+8).toNat+4≤p.out548.toNat ∨ p.out548.toNat+8≤(scratch p+16+8).toNat) :
    readI32 (finalMemory p) (p.out548.toNat+8)=p.size := by
  have b := result_bounds p hn ha
  have high := StateReadResult.finalMemory_read_high_original (registeredMemory p) p.out548 (scratch p+16)
    b.1 b.2.1 b.2.2.2.1 hs
  rw [b.2.2.2.2.2.1,b.2.2.2.2.2.2] at high
  unfold finalMemory
  exact high.trans (registeredMemory_record p hn ha).2.2

theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (ha : p.allocator=1074896)
    (j : Nat) (hj : j<p.out548.toNat ∨ p.out548.toNat+12≤j) :
    (finalMemory p).read8 j=(registeredMemory p).read8 j := by
  have b := result_bounds p hn ha
  unfold finalMemory
  exact StateReadResult.finalMemory_outside (registeredMemory p) p.out548 (scratch p+16)
    b.1 b.2.1 b.2.2.2.1 b.2.2.2.2.2.1 j hj
end WNear.Proofs.StateReadStorageOuter
