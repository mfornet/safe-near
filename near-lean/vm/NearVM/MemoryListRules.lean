import Wasm.MemoryLemmas

/-! Byte-level specifications of the actual whole-register memory write. -/
namespace Wasm.Memory

theorem writeList_nil (memory : Memory) (address : Nat) :
    memory.writeList address [] = memory := by
  unfold writeList
  rfl

theorem writeList_cons (memory : Memory) (address : Nat) (byte : UInt8) (bytes : List UInt8) :
    memory.writeList address (byte :: bytes) =
      (if address < memory.byteSize then memory.write8 address byte else memory).writeList
        (address + 1) bytes := by
  unfold writeList
  rfl

/-- A bounded list write replaces precisely its byte interval, including overlapping
source data already materialized in the host register. -/
theorem writeList_spec (bytes : List UInt8) (memory : Memory) (address : Nat)
    (hwf : memory.wf) (hbound : address + bytes.length ≤ memory.byteSize) :
    (memory.writeList address bytes).wf ∧
    (memory.writeList address bytes).byteSize = memory.byteSize ∧
    (memory.writeList address bytes).max = memory.max ∧
    ∀ j, (memory.writeList address bytes).read8 j =
      if address ≤ j ∧ j < address + bytes.length then bytes[j - address]! else memory.read8 j := by
  induction bytes generalizing memory address with
  | nil =>
    simp [writeList_nil, hwf]
    omega
  | cons byte bytes ih =>
    have ha : address < memory.byteSize := by simp only [List.length_cons] at hbound; omega
    rw [writeList_cons, ite_eq_left ha]
    have hs := ih (memory.write8 address byte) (address + 1) (write8_wf hwf _ _)
      (by simp only [write8_byteSize, List.length_cons] at *; omega)
    refine ⟨hs.1, hs.2.1.trans (write8_byteSize _ _ _), hs.2.2.1.trans (write8_max _ _ _), ?_⟩
    intro j
    rw [hs.2.2.2, read8_write8 hwf ha]
    by_cases heq : j = address
    · subst j
      have hn : ¬ address + 1 ≤ address := by omega
      simp [hn]
    · by_cases hj : address ≤ j ∧ j < address + (byte :: bytes).length
      · have hj' : address + 1 ≤ j ∧ j < address + 1 + bytes.length := by
          simp only [List.length_cons] at hj
          omega
        have hsub : j - address = (j - (address + 1)) + 1 := by omega
        rw [ite_eq_left hj', ite_eq_left hj, hsub, List.getElem!_cons_succ]
      · have hj' : ¬ (address + 1 ≤ j ∧ j < address + 1 + bytes.length) := by
          simp only [List.length_cons] at hj
          omega
        simp only [hj, hj', heq, ite_false]

theorem readList_writeList (bytes : List UInt8) (memory : Memory) (address : Nat)
    (hwf : memory.wf) (hbound : address + bytes.length ≤ memory.byteSize) :
    (memory.writeList address bytes).readList address bytes.length = bytes := by
  have hs := writeList_spec bytes memory address hwf hbound
  unfold readList
  apply List.ext_getElem
  · simp
  · intro k h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    rw [hs.2.2.2]
    have hk : address ≤ address + k ∧ address + k < address + bytes.length := by omega
    rw [ite_eq_left hk]
    simp only [Nat.add_sub_cancel_left, getElem!_pos bytes k h₂]

end Wasm.Memory
