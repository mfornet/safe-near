import Proofs.InterfaceLazyNative
import Proofs.ValueReturnOuterLayout

/-! Actual initialized status/counter/receiver readback for separated native spans. -/
namespace WNear.Proofs.InterfaceLazyReadback
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceLazyComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] writeI32 writeI64 readI32 readI64

/-- The initialized status is one and the complete eight-byte counter/receiver
payload is zero. The vtable scratch word is not claimed to be initialized. -/
theorem spec (p : Layout) (hr : InterfaceLazyNative.Native p) :
    (InterfaceLazyLayout.finalMemory p).wf ∧
    (InterfaceLazyLayout.finalMemory p).byteSize = p.memory.byteSize ∧
    (InterfaceLazyLayout.finalMemory p).max = p.memory.max ∧
    ∀ j, p.cell.toNat ≤ j → j < p.cell.toNat + 12 →
      (InterfaceLazyLayout.finalMemory p).read8 j =
        if j < p.cell.toNat + 4 then UInt8.ofNat ((1 : UInt32).toNat >>> (8 * (j - p.cell.toNat))) else 0 := by
  let t := tailLayout p
  have hb := InterfaceLazyNative.bounds p hr
  have hi : (scratch p).toNat + 8 ≤ p.memory.byteSize := by have h := hr.scratchSpan; omega
  have h0 := writeI64_spec p.memory (scratch p).toNat 0 hr.wf hi
  have h1 := writeI64_spec t.memory (t.cell.toNat + 4) (readI64 t.memory t.scratch.toNat) h0.1 (by have h := hb.highCell; omega)
  have h2 := writeI32_spec (InterfaceLazyState.highMemory t) (t.cell + 12).toNat
    (readI32 (InterfaceLazyState.highMemory t) (t.scratch + 8).toNat) h1.1 hb.wordCell
  have h3 := writeI32_spec (InterfaceLazyState.wordMemory t) t.cell.toNat 1 h2.1 hb.statusCell
  have h4 := writeI32_spec (InterfaceLazyState.statusMemory t) ((t.scratch + 16) + 12).toNat (InterfaceLazyState.oldHigh t) h3.1 hb.saveHigh
  have h5 := writeI32_spec (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t))
    (t.scratch.toNat + 16) (InterfaceLazyState.oldStatus t) h4.1 (by have h := hb.saveStatus; omega)
  have h6 := writeI64_spec (InterfaceLazySaved.statusMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldStatus t) (InterfaceLazyState.oldHigh t))
    (t.scratch.toNat + 20) (InterfaceLazyState.oldLow t) h5.1 (by have h := hb.saveLow; omega)
  have rz : readI64 t.memory t.scratch.toNat = 0 := by
    simpa only [t, tailLayout] using InterfaceInitialize.zero_word p.memory (scratch p).toNat hr.wf hi
  have hc12 : (t.cell + 12).toNat = t.cell.toNat + 12 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    have h := hr.cell; have w := hr.width; dsimp only [t, tailLayout]; omega
  have hs28 : ((t.scratch + 16) + 12).toNat = t.scratch.toNat + 28 := by
    rw [UInt32.toNat_add, UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    have h := hr.scratchSpan; have w := hr.width; dsimp only [t, tailLayout]; omega
  have fWf : (InterfaceLazyLayout.finalMemory p).wf := h6.1
  have size0 : t.memory.byteSize = p.memory.byteSize := h0.2.1
  have size1 : (InterfaceLazyState.highMemory t).byteSize = t.memory.byteSize := h1.2.1
  have size2 : (InterfaceLazyState.wordMemory t).byteSize = (InterfaceLazyState.highMemory t).byteSize := h2.2.1
  have size3 : (InterfaceLazyState.statusMemory t).byteSize = (InterfaceLazyState.wordMemory t).byteSize := h3.2.1
  have size4 : (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t)).byteSize =
      (InterfaceLazyState.statusMemory t).byteSize := h4.2.1
  have size5 : (InterfaceLazySaved.statusMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldStatus t) (InterfaceLazyState.oldHigh t)).byteSize =
      (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t)).byteSize := h5.2.1
  have size6 : (InterfaceLazyLayout.finalMemory p).byteSize =
      (InterfaceLazySaved.statusMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldStatus t) (InterfaceLazyState.oldHigh t)).byteSize := h6.2.1
  have fs : (InterfaceLazyLayout.finalMemory p).byteSize = p.memory.byteSize := by rw [size6, size5, size4, size3, size2, size1, size0]
  have fm : (InterfaceLazyLayout.finalMemory p).max = p.memory.max :=
    h6.2.2.1.trans (h5.2.2.1.trans (h4.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans (h1.2.2.1.trans h0.2.2.1)))))
  refine ⟨fWf, fs, fm, ?_⟩
  intro j hj hlt
  have sep : t.scratch.toNat + 48 ≤ t.cell.toNat ∨ t.cell.toNat + 16 ≤ t.scratch.toNat := hr.separated
  have hjt : t.cell.toNat ≤ j ∧ j < t.cell.toNat + 12 := ⟨hj, hlt⟩
  have n6 : ¬(t.scratch.toNat + 20 ≤ j ∧ j < t.scratch.toNat + 20 + 8) := by omega
  have n5 : ¬(t.scratch.toNat + 16 ≤ j ∧ j < t.scratch.toNat + 16 + 4) := by omega
  have n4 : ¬(((t.scratch + 16) + 12).toNat ≤ j ∧ j < ((t.scratch + 16) + 12).toNat + 4) := by rw [hs28]; omega
  change (writeI64 (InterfaceLazySaved.statusMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldStatus t) (InterfaceLazyState.oldHigh t))
    (t.scratch.toNat + 20) (InterfaceLazyState.oldLow t)).read8 j = _
  rw [h6.2.2.2, ite_eq_right n6]
  change (writeI32 (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t))
    (t.scratch.toNat + 16) (InterfaceLazyState.oldStatus t)).read8 j = _
  rw [h5.2.2.2, ite_eq_right n5]
  change (writeI32 (InterfaceLazyState.statusMemory t) ((t.scratch + 16) + 12).toNat (InterfaceLazyState.oldHigh t)).read8 j = _
  rw [h4.2.2.2, ite_eq_right n4]
  change (writeI32 (InterfaceLazyState.wordMemory t) t.cell.toNat 1).read8 j = _
  rw [h3.2.2.2]
  by_cases first : j < t.cell.toNat + 4
  · have inside : t.cell.toNat ≤ j ∧ j < t.cell.toNat + 4 := ⟨hjt.1, first⟩
    have first' : j < p.cell.toNat + 4 := by simpa only [t, tailLayout] using first
    rw [ite_eq_left inside, ite_eq_left first']
    rfl
  · have outside : ¬(t.cell.toNat ≤ j ∧ j < t.cell.toNat + 4) := by omega
    have first' : ¬(j < p.cell.toNat + 4) := by simpa only [t, tailLayout] using first
    rw [ite_eq_right outside, ite_eq_right first']
    change (writeI32 (InterfaceLazyState.highMemory t) (t.cell + 12).toNat
      (readI32 (InterfaceLazyState.highMemory t) (t.scratch + 8).toNat)).read8 j = 0
    have n2 : ¬((t.cell + 12).toNat ≤ j ∧ j < (t.cell + 12).toNat + 4) := by rw [hc12]; omega
    rw [h2.2.2.2, ite_eq_right n2]
    change (writeI64 t.memory (t.cell.toNat + 4) (readI64 t.memory t.scratch.toNat)).read8 j = 0
    have inside : t.cell.toNat + 4 ≤ j ∧ j < t.cell.toNat + 4 + 8 := by omega
    rw [h1.2.2.2, ite_eq_left inside, rz]
    simp only [UInt64.toNat_zero, Nat.zero_shiftRight]
    rfl

theorem status_word (p : Layout) (hr : InterfaceLazyNative.Native p) :
    readI32 (InterfaceLazyLayout.finalMemory p) p.cell.toNat = 1 := by
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  have byte := (spec p hr).2.2.2 (p.cell.toNat + i) (by omega) (by omega)
  have inside : p.cell.toNat + i < p.cell.toNat + 4 := by omega
  rw [ite_eq_left inside] at byte
  simpa only [Nat.add_sub_cancel_left] using byte

/-- Every in-range unaligned four-byte subword of the eight zero bytes is zero. -/
theorem zero_word (p : Layout) (hr : InterfaceLazyNative.Native p) (offset : Nat)
    (ho : 4 ≤ offset) (he : offset ≤ 8) :
    readI32 (InterfaceLazyLayout.finalMemory p) (p.cell.toNat + offset) = 0 := by
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  have byte := (spec p hr).2.2.2 (p.cell.toNat + offset + i) (by omega) (by omega)
  have outside : ¬(p.cell.toNat + offset + i < p.cell.toNat + 4) := by omega
  rw [ite_eq_right outside] at byte
  simpa only [UInt32.toNat_zero, Nat.zero_shiftRight, show UInt8.ofNat 0 = (0 : UInt8) from rfl] using byte

theorem counter_word (p : Layout) (hr : InterfaceLazyNative.Native p) :
    readI32 (InterfaceLazyLayout.finalMemory p) (p.cell.toNat + 4) = 0 := zero_word p hr 4 (by omega) (by omega)

theorem receiver_word (p : Layout) (hr : InterfaceLazyNative.Native p) :
    readI32 (InterfaceLazyLayout.finalMemory p) (p.cell.toNat + 8) = 0 := zero_word p hr 8 (by omega) (by omega)

end WNear.Proofs.InterfaceLazyReadback
