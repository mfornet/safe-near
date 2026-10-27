import Proofs.ValueReturnOuterState
import Proofs.ValueReturnSlice
import Proofs.LoadedValueReturnData

/-! Snapshot layout facts for the actual sequential outer-method writes.
All disjointness is stated as native byte intervals; no alignment is assumed. -/
namespace WNear.Proofs.ValueReturnOuterLayout
open Wasm Wasm.Near MeteredLogic
open ValueReturnOuterBody
set_option maxRecDepth 16384
attribute [local irreducible] acquiredMemory highMemory lowMemory borrowed writeI32 readI32

/-- Reading four specified little-endian bytes recovers the original u32. -/
theorem readI32_of_bytes (memory : Memory) (address : Nat) (value : UInt32)
    (hbytes : ∀ i, i < 4 → memory.read8 (address + i) = UInt8.ofNat (value.toNat >>> (8 * i))) :
    readI32 memory address = value := by
  have hm : (List.range 4).map (fun i => memory.read8 (address + i)) =
      (List.range 4).map (fun i => UInt8.ofNat (value.toNat >>> (8 * i))) := by
    apply List.map_congr_left
    intro i hi
    exact hbytes i (List.mem_range.mp hi)
  have hd := congrArg Memory.decodeLE hm
  rw [ValueReturnSlice.decode_word] at hd
  have hr : readI32 memory address = UInt32.ofNat
      (Memory.decodeLE ((List.range 4).map (fun i => memory.read8 (address + i)))) := by
    simp [readI32, Memory.decodeLE, List.foldr_map]
  rw [hr, hd, UInt32.ofNat_toNat]

/-- The acquisition writes its complete scratch record after updating the
counter, so its two record words need no scratch/counter disjointness. -/
theorem acquired_spec (p : Layout) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 8 ≤ p.memory.byteSize) :
    (acquiredMemory p).wf ∧ (acquiredMemory p).byteSize = p.memory.byteSize ∧
    (acquiredMemory p).max = p.memory.max ∧
    readI32 (acquiredMemory p) (scratch p).toNat = 1074908 ∧
    readI32 (acquiredMemory p) ((scratch p).toNat + 4) = 1074904 ∧
    ∀ j, (j < 1074904 ∨ 1074908 ≤ j) →
      (j < (scratch p).toNat ∨ (scratch p).toNat + 8 ≤ j) →
      (acquiredMemory p).read8 j = p.memory.read8 j := by
  let first := writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904)
  have hs1 := writeI32_spec p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904) hwf hcell
  have hb2 : (scratch p).toNat + 4 + 4 ≤ first.byteSize := by rw [show first.byteSize = p.memory.byteSize from hs1.2.1]; omega
  have hs2 := writeI32_spec first ((scratch p).toNat + 4) 1074904 hs1.1 hb2
  have hb3 : (scratch p).toNat + 4 ≤ (writeI32 first ((scratch p).toNat + 4) 1074904).byteSize := by
    rw [hs2.2.1, show first.byteSize = p.memory.byteSize from hs1.2.1]; omega
  have hs3 := writeI32_spec (writeI32 first ((scratch p).toNat + 4) 1074904)
    (scratch p).toNat 1074908 hs2.1 hb3
  have he : acquiredMemory p = writeI32 (writeI32 first ((scratch p).toNat + 4) 1074904) (scratch p).toNat 1074908 := by
    unfold acquiredMemory ValueReturnAcquire.recordMemory
    rfl
  rw [he]
  refine ⟨hs3.1, hs3.2.1.trans (hs2.2.1.trans hs1.2.1),
    hs3.2.2.1.trans (hs2.2.2.1.trans hs1.2.2.1), ?_, ?_, ?_⟩
  · apply readI32_of_bytes
    intro i hi
    rw [hs3.2.2.2]
    have hn : (scratch p).toNat ≤ (scratch p).toNat + i ∧ (scratch p).toNat + i < (scratch p).toNat + 4 := by omega
    simp [hn]
  · apply readI32_of_bytes
    intro i hi
    rw [hs3.2.2.2, hs2.2.2.2]
    have ho : ¬ ((scratch p).toNat ≤ (scratch p).toNat + 4 + i ∧ (scratch p).toNat + 4 + i < (scratch p).toNat + 4) := by omega
    have hn : (scratch p).toNat + 4 ≤ (scratch p).toNat + 4 + i ∧ (scratch p).toNat + 4 + i < (scratch p).toNat + 4 + 4 := by omega
    simp [ho, hn]
  · intro j hc hs
    rw [hs3.2.2.2, hs2.2.2.2, hs1.2.2.2]
    have h3 : ¬ ((scratch p).toNat ≤ j ∧ j < (scratch p).toNat + 4) := by omega
    have h2 : ¬ ((scratch p).toNat + 4 ≤ j ∧ j < (scratch p).toNat + 4 + 4) := by omega
    have h1 : ¬ (1074904 ≤ j ∧ j < 1074904 + 4) := by omega
    simp [h3, h2, h1]

/-- The pointer loaded from the acquired scratch record is the fixed cell's
payload pointer, independently of the original counter and all byte aliasing. -/
theorem borrowed_eq (p : Layout) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 16 ≤ p.memory.byteSize) : borrowed p = 1074908 := by
  have ha := acquired_spec p hwf hcell (by omega)
  have hh := writeI32_spec (acquiredMemory p) ((scratch p).toNat + 12)
    (readI32 (acquiredMemory p) ((scratch p).toNat + 4)) ha.1 (by rw [ha.2.1]; omega)
  unfold borrowed highMemory
  apply Eq.trans (LoadedValueReturnData.readI32_frame _ _ _ ?_) ha.2.2.2.1
  intro i hi
  rw [hh.2.2.2]
  have ho : ¬ ((scratch p).toNat + 12 ≤ (scratch p).toNat + i ∧ (scratch p).toNat + i < (scratch p).toNat + 12 + 4) := by omega
  rw [ite_eq_right ho]

/-- Exact footprint of all five outer writes up to dispatch selection. -/
theorem low_spec (p : Layout) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 16 ≤ p.memory.byteSize) :
    (lowMemory p).wf ∧ (lowMemory p).byteSize = p.memory.byteSize ∧
    (lowMemory p).max = p.memory.max ∧
    ∀ j, (j < 1074904 ∨ 1074908 ≤ j) →
      (j < (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ j) →
      (lowMemory p).read8 j = p.memory.read8 j := by
  have ha := acquired_spec p hwf hcell (by omega)
  have hh := writeI32_spec (acquiredMemory p) ((scratch p).toNat + 12)
    (readI32 (acquiredMemory p) ((scratch p).toNat + 4)) ha.1 (by rw [ha.2.1]; omega)
  have heHigh : highMemory p = writeI32 (acquiredMemory p) ((scratch p).toNat + 12)
      (readI32 (acquiredMemory p) ((scratch p).toNat + 4)) := by unfold highMemory; rfl
  rw [← heHigh] at hh
  have hb : (scratch p).toNat + 8 + 4 ≤ (highMemory p).byteSize := by
    rw [hh.2.1, ha.2.1]; omega
  have hl := writeI32_spec (highMemory p) ((scratch p).toNat + 8) (borrowed p) hh.1 hb
  have heLow : lowMemory p = writeI32 (highMemory p) ((scratch p).toNat + 8) (borrowed p) := by
    unfold lowMemory; rfl
  rw [← heLow] at hl
  refine ⟨hl.1, hl.2.1.trans (hh.2.1.trans ha.2.1), hl.2.2.1.trans (hh.2.2.1.trans ha.2.2.1), ?_⟩
  intro j hc hs
  rw [hl.2.2.2, hh.2.2.2]
  have ho8 : ¬ ((scratch p).toNat + 8 ≤ j ∧ j < (scratch p).toNat + 8 + 4) := by omega
  have ho12 : ¬ ((scratch p).toNat + 12 ≤ j ∧ j < (scratch p).toNat + 12 + 4) := by omega
  simp only [ho8, ho12, ↓reduceIte]
  exact ha.2.2.2.2.2 j hc (by omega)

/-- Any four-byte snapshot word outside the exact counter/scratch footprint
is retained, including receiver, vtable, dispatch-table and slice words. -/
theorem low_read_frame (p : Layout) (address : Nat) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (hc : address + 4 ≤ 1074904 ∨ 1074908 ≤ address)
    (hs : address + 4 ≤ (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ address) :
    readI32 (lowMemory p) address = readI32 p.memory address := by
  have hl := low_spec p hwf hcell hspan
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  exact hl.2.2.2 (address + i) (by omega) (by omega)

/-- The same exact footprint preserves the zero-extended pointer and length
words consumed by the deployed dispatch loads. -/
theorem low_packed32_frame (p : Layout) (address : Nat) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (hc : address + 4 ≤ 1074904 ∨ 1074908 ≤ address)
    (hs : address + 4 ≤ (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ address) :
    ValueReturnDispatch.packed32 (lowMemory p) address = ValueReturnDispatch.packed32 p.memory address := by
  have hl := low_spec p hwf hcell hspan
  have hm : (List.range 4).map (fun i => (lowMemory p).read8 (address + i)) =
      (List.range 4).map (fun i => p.memory.read8 (address + i)) := by
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    exact hl.2.2.2 (address + i) (by omega) (by omega)
  have hd := congrArg (fun bytes => UInt64.ofNat (Memory.decodeLE bytes)) hm
  simpa only [ValueReturnDispatch.packed32, Memory.decodeLE, List.foldr_map] using hd

/-- An original nonzero receiver word selects the fixed payload pointer when
the scratch writes do not overlap that word. -/
theorem selected_eq (p : Layout) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (hs : 1074912 ≤ (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ 1074908)
    (hn : readI32 p.memory 1074908 ≠ 0) : selected p = 1074908 := by
  have hb := borrowed_eq p hwf hcell hspan
  have hf := low_read_frame p 1074908 hwf hcell hspan (Or.inr (by omega)) hs
  unfold selected
  rw [hb]
  change (if readI32 (lowMemory p) 1074908 ≠ 0 then 1074908 else 0) = 1074908
  rw [hf, ite_eq_left hn]

/-- The total memory reader depends only on the requested bytes. Bounds are
unnecessary: its out-of-bounds behavior is already included in read8. -/
theorem readList_frame (before after : Memory) (address length : Nat)
    (hbytes : ∀ i < length, after.read8 (address + i) = before.read8 (address + i)) :
    after.readList address length = before.readList address length := by
  unfold Memory.readList
  apply List.map_congr_left
  intro i hi
  exact hbytes i (List.mem_range.mp hi)

/-- The complete payload remains the original snapshot exactly when its span
is disjoint from the counter and scratch write intervals. -/
theorem lowMemory_payload_frame (p : Layout) (address length : Nat) (hwf : p.memory.wf)
    (hcell : 1074904 + 4 ≤ p.memory.byteSize)
    (hspan : (scratch p).toNat + 16 ≤ p.memory.byteSize)
    (hc : address + length ≤ 1074904 ∨ 1074908 ≤ address)
    (hs : address + length ≤ (scratch p).toNat ∨ (scratch p).toNat + 16 ≤ address) :
    (lowMemory p).readList address length = p.memory.readList address length := by
  have hl := low_spec p hwf hcell hspan
  apply readList_frame
  intro i hi
  exact hl.2.2.2 (address + i) (by omega) (by omega)

end WNear.Proofs.ValueReturnOuterLayout
