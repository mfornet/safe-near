import Proofs.AllocateSearchState
import Proofs.AllocateSplitReadback

/-! Original native intervals derive the readbacks of every sequential split write. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

structure Shape (p : Layout) (memory : Memory) : Prop where
  wf : memory.wf
  size : memory.byteSize = p.memory.byteSize
  max : memory.max = p.memory.max

theorem intervals (p : Layout) (hn : Native p) :
    (head p).toNat+72 ≤ (header p).toNat ∧
    (header p).toNat+12 ≤ (finish p).toNat ∧ (finish p).toNat+8 ≤ p.memory.byteSize := by
  have ptr := Allocate.split_pointer_toNat p.memory (head p) p.words hn.split
  have hdr := Allocate.split_header_toNat p.memory (head p) p.words hn.split
  have room := hn.split.room
  have positive := hn.split.wordsPositive
  change (head p).toNat+72 ≤ (Allocate.splitHeader p.memory (head p) p.words).toNat ∧ _
  change _ ∧ (Allocate.splitHeader p.memory (head p) p.words).toNat+12 ≤
    (Allocate.endWord p.memory (head p)).toNat ∧ _
  exact ⟨by omega,by omega,hn.endBound⟩

private theorem write_shape (p : Layout) (m : Memory) (shape : Shape p m) (address : Nat) (value : UInt32)
    (hb : address+4 ≤ p.memory.byteSize) : Shape p (writeI32 m address value) := by
  have h := writeI32_spec m address value shape.wf (by rw [shape.size]; exact hb)
  exact ⟨h.1,h.2.1.trans shape.size,h.2.2.1.trans shape.max⟩

theorem cleared_shape (p : Layout) (hn : Native p) : Shape p (clearedMemory p) := by
  have bounds := intervals p hn
  have h := Allocate.clearedMemory_spec p.memory (header p) hn.memoryWf (by omega)
  exact ⟨h.1,h.2.1,h.2.2.1⟩
theorem initialized_shape (p : Layout) (hn : Native p) : Shape p (initializedMemory p) := by
  have bounds := intervals p hn
  exact write_shape p (clearedMemory p) (cleared_shape p hn) _ _ (by omega)
theorem backlinked_shape (p : Layout) (hn : Native p) : Shape p (backlinkedMemory p) := by
  have bounds := intervals p hn
  exact write_shape p (initializedMemory p) (initialized_shape p hn) _ _ (by omega)
theorem previous_shape (p : Layout) (hn : Native p) : Shape p (previousMemory p) := by
  have bounds := intervals p hn
  exact write_shape p (backlinkedMemory p) (backlinked_shape p hn) _ _ (by omega)
theorem unflagged_shape (p : Layout) (hn : Native p) : Shape p (unflaggedMemory p) := by
  have bounds := intervals p hn
  exact write_shape p (previousMemory p) (previous_shape p hn) _ _ (by omega)
theorem linked_shape (p : Layout) (hn : Native p) : Shape p (linkedMemory p) := by
  have bounds := intervals p hn
  exact write_shape p (unflaggedMemory p) (unflagged_shape p hn) _ _ (by omega)
theorem final_shape (p : Layout) (hn : Native p) : Shape p (finalMemory p) := by
  have bounds := intervals p hn
  exact write_shape p (linkedMemory p) (linked_shape p hn) _ _ (by omega)

private theorem frame_read (p : Layout) (m : Memory) (shape : Shape p m) (address target : Nat) (value : UInt32)
    (hb : address+4 ≤ p.memory.byteSize) (hd : target+4 ≤ address ∨ address+4 ≤ target) :
    readI32 (writeI32 m address value) target = readI32 m target :=
  PanicAllocateReadback.read_write_frame m target address value shape.wf (by rw [shape.size]; exact hb) hd
private theorem self_read (p : Layout) (m : Memory) (shape : Shape p m) (address : Nat) (value : UInt32)
    (hb : address+4 ≤ p.memory.byteSize) : readI32 (writeI32 m address value) address = value :=
  PanicAllocateReadback.read_write_self m address value shape.wf (by rw [shape.size]; exact hb)

theorem initialized_reads (p : Layout) (hn : Native p) :
    readI32 (initializedMemory p) (head p).toNat = readI32 p.memory (head p).toNat ∧
    readI32 (initializedMemory p) (header p).toNat = finish p ∧
    readI32 (initializedMemory p) ((header p).toNat+4) = 0 := by
  have b := intervals p hn
  have h := Allocate.initializedMemory_spec p.memory (head p) (header p) hn.memoryWf (by omega) (by omega)
  have z := Allocate.initialized_high_zero p.memory (head p) (header p) hn.memoryWf (by omega)
  exact ⟨h.2.2.2.2.1,h.2.2.2.1,z⟩

theorem initialized_candidate (p : Layout) (hn : Native p) :
    readI32 (initializedMemory p) ((head p).toNat+8) = readI32 p.memory ((head p).toNat+8) := by
  have b := intervals p hn
  have h := Allocate.initializedMemory_spec p.memory (head p) (header p) hn.memoryWf (by omega) (by omega)
  apply Allocate.readI32_congr_bytes
  intro i hi
  exact h.2.2.2.2.2 _ (Or.inl (by omega))

theorem backlinked_header_high (p : Layout) (hn : Native p) :
    readI32 (backlinkedMemory p) ((header p).toNat+4) = 0 := by
  have b := intervals p hn
  exact (frame_read p _ (initialized_shape p hn) ((finish p).toNat+4) ((header p).toNat+4) _
    (by omega) (Or.inl (by omega))).trans (initialized_reads p hn).2.2

theorem previous_candidate (p : Layout) (hn : Native p) :
    readI32 (previousMemory p) ((head p).toNat+8) = readI32 p.memory ((head p).toNat+8) := by
  have b := intervals p hn
  have previous := frame_read p _ (backlinked_shape p hn) ((header p).toNat+4) ((head p).toNat+8) (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) (by omega) (Or.inl (by omega))
  have backlink := frame_read p _ (initialized_shape p hn) ((finish p).toNat+4) ((head p).toNat+8) (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)) (by omega) (Or.inl (by omega))
  exact previous.trans (backlink.trans (initialized_candidate p hn))

theorem unflagged_head (p : Layout) (hn : Native p) :
    readI32 (unflaggedMemory p) (head p).toNat = readI32 p.memory (head p).toNat := by
  have b := intervals p hn
  have unflag := frame_read p _ (previous_shape p hn) ((head p).toNat+8) (head p).toNat (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294) (by omega) (Or.inl (by omega))
  have previous := frame_read p _ (backlinked_shape p hn) ((header p).toNat+4) (head p).toNat (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) (by omega) (Or.inl (by omega))
  have backlink := frame_read p _ (initialized_shape p hn) ((finish p).toNat+4) (head p).toNat (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)) (by omega) (Or.inl (by omega))
  exact unflag.trans (previous.trans (backlink.trans (initialized_reads p hn).1))

theorem unflagged_header (p : Layout) (hn : Native p) :
    readI32 (unflaggedMemory p) (header p).toNat = finish p := by
  have b := intervals p hn
  have unflag := frame_read p _ (previous_shape p hn) ((head p).toNat+8) (header p).toNat (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294) (by omega) (Or.inr (by omega))
  have previous := frame_read p _ (backlinked_shape p hn) ((header p).toNat+4) (header p).toNat (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) (by omega) (Or.inl (by omega))
  have backlink := frame_read p _ (initialized_shape p hn) ((finish p).toNat+4) (header p).toNat (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)) (by omega) (Or.inl (by omega))
  exact unflag.trans (previous.trans (backlink.trans (initialized_reads p hn).2.1))

theorem linked_reads (p : Layout) (hn : Native p) :
    readI32 (linkedMemory p) (head p).toNat = header p ∧
    readI32 (linkedMemory p) (header p).toNat = finish p := by
  have b := intervals p hn
  have self := self_read p _ (unflagged_shape p hn) (head p).toNat
    (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)) (by omega)
  have value : Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p) = header p := by
    simp only [Allocate.taggedValue,Nat.add_zero,unflagged_head p hn,hn.headFlags,UInt32.zero_or]
  have other := frame_read p _ (unflagged_shape p hn) (head p).toNat (header p).toNat (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)) (by omega) (Or.inr (by omega))
  exact ⟨self.trans value,other.trans (unflagged_header p hn)⟩

theorem finish_original (p : Layout) (hn : Native p) : finish p = readI32 p.memory (head p).toNat := by
  have flags := congrArg UInt32.toBitVec hn.headFlags
  simp only [UInt32.toBitVec_and] at flags
  apply UInt32.toBitVec_inj.mp
  change (readI32 p.memory (head p).toNat).toBitVec &&& (4294967292 : UInt32).toBitVec = _
  have dist := BitVec.and_or_distrib_left (x := (readI32 p.memory (head p).toNat).toBitVec)
    (y := (4294967292 : UInt32).toBitVec) (z := (3 : UInt32).toBitVec)
  simp only [show (4294967292 : UInt32).toBitVec ||| (3 : UInt32).toBitVec = BitVec.allOnes 32 by decide,
    BitVec.and_allOnes, flags, show (0 : UInt32).toBitVec = 0#32 by rfl, BitVec.or_zero] at dist
  exact dist.symm

theorem initialized_head_finish (p : Layout) (hn : Native p) :
    readI32 (initializedMemory p) (head p).toNat = finish p :=
  (initialized_reads p hn).1.trans (finish_original p hn).symm

theorem previous_header_high (p : Layout) (hn : Native p) :
    readI32 (previousMemory p) ((header p).toNat+4) = head p := by
  have b := intervals p hn
  have self := self_read p _ (backlinked_shape p hn) ((header p).toNat+4)
    (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) (by omega)
  have value : Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p) = head p := by
    simp only [Allocate.taggedValue,backlinked_header_high p hn,UInt32.zero_and,UInt32.zero_or]
  exact self.trans value

private theorem low_mod (value : UInt32) : (value &&& 3).toNat = value.toNat % 4 := by
  rw [UInt32.toNat_and]
  change value.toNat &&& (2^2-1) = value.toNat % 2^2
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem header_aligned (p : Layout) (hn : Native p) : header p &&& 3 = 0 := by
  have masked : finish p &&& 3 = 0 := by
    simp only [finish,Allocate.endWord,UInt32.and_assoc,show (4294967292 : UInt32) &&& 3 = 0 by decide,UInt32.and_zero]
  have finishMod : (finish p).toNat % 4 = 0 := by
    have h := congrArg UInt32.toNat masked
    simpa only [low_mod,UInt32.toNat_zero] using h
  have ptr := Allocate.split_pointer_toNat p.memory (head p) p.words hn.split
  have hdr := Allocate.split_header_toNat p.memory (head p) p.words hn.split
  have room := hn.split.room
  apply UInt32.toNat_inj.mp
  rw [low_mod]
  change (Allocate.splitHeader p.memory (head p) p.words).toNat % 4 = 0
  change (Allocate.endWord p.memory (head p)).toNat % 4 = 0 at finishMod
  omega

end WNear.Proofs.AllocateSearch
