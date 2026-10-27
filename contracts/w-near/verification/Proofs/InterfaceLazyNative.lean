import Proofs.InterfaceLazyLayout
import Proofs.LoadedValueReturnData

/-! Native span conditions discharge the lazy body's sequential memory bounds. -/
namespace WNear.Proofs.InterfaceLazyNative
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceLazyComplete
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] writeI32 writeI64 readI32 readI64

/-- The two regions are separated only in this readback corollary. Operational
body and call contracts continue to retain arbitrary aliasing. -/
structure Native (p : Layout) : Prop where
  wf : p.memory.wf
  width : p.memory.byteSize ≤ 2 ^ 32
  cell : p.cell.toNat + 16 ≤ p.memory.byteSize
  scratchSpan : (scratch p).toNat + 48 ≤ p.memory.byteSize
  separated : (scratch p).toNat + 48 ≤ p.cell.toNat ∨ p.cell.toNat + 16 ≤ (scratch p).toNat
  empty : readI32 p.memory p.cell.toNat = 0

private theorem add_small (v : UInt32) (n : Nat) (hn : n < 2 ^ 32)
    (hb : v.toNat + n < 2 ^ 32) : (v + UInt32.ofNat n).toNat = v.toNat + n := by
  rw [UInt32.toNat_add, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hb]

/-- All body bounds and its real old-status-zero condition follow from initial
memory/spans and initial status zero; no computed memory lookup is assumed. -/
theorem bounds (p : Layout) (hr : Native p) : InterfaceLazyTail.Bounds (tailLayout p) := by
  let t := tailLayout p
  have hc12 : (p.cell + 12).toNat = p.cell.toNat + 12 := by
    apply add_small p.cell 12 (by decide)
    have hc := hr.cell; have hw := hr.width; omega
  have hs8 : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    apply add_small (scratch p) 8 (by decide)
    have hs := hr.scratchSpan; have hw := hr.width; omega
  have hs16 : (scratch p + 16).toNat = (scratch p).toNat + 16 := by
    apply add_small (scratch p) 16 (by decide)
    have hs := hr.scratchSpan; have hw := hr.width; omega
  have hs28 : ((scratch p + 16) + 12).toNat = (scratch p).toNat + 28 := by
    have h := add_small (scratch p + 16) 12 (by decide) (by rw [hs16]; have hs := hr.scratchSpan; have hw := hr.width; omega)
    change (scratch p + 16 + (UInt32.ofNat 12)).toNat = (scratch p).toNat + 28
    rw [h, hs16]
  have ib : (scratch p).toNat + 8 ≤ p.memory.byteSize := by have hs := hr.scratchSpan; omega
  have h0 := writeI64_spec p.memory (scratch p).toNat 0 hr.wf ib
  have hc : t.cell.toNat + 12 ≤ t.memory.byteSize := by
    dsimp only [t, tailLayout]
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h0.2.1]
    have hc := hr.cell; omega
  have hs : t.scratch.toNat + 8 ≤ t.memory.byteSize := by
    dsimp only [t, tailLayout]; rw [h0.2.1]; exact ib
  have h1 := writeI64_spec t.memory (t.cell.toNat + 4) (readI64 t.memory t.scratch.toNat) h0.1 (by omega)
  have wc : (t.cell + 12).toNat + 4 ≤ (InterfaceLazyState.highMemory t).byteSize := by
    change (p.cell + 12).toNat + 4 ≤ (writeI64 t.memory (t.cell.toNat + 4) (readI64 t.memory t.scratch.toNat)).byteSize
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h1.2.1, h0.2.1, hc12]; exact hr.cell
  have ws : (t.scratch + 8).toNat + 4 ≤ (InterfaceLazyState.highMemory t).byteSize := by
    change (scratch p + 8).toNat + 4 ≤ (writeI64 t.memory (t.cell.toNat + 4) (readI64 t.memory t.scratch.toNat)).byteSize
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h1.2.1, h0.2.1, hs8]; have hb := hr.scratchSpan; omega
  have h2 := writeI32_spec (InterfaceLazyState.highMemory t) (t.cell + 12).toNat
    (readI32 (InterfaceLazyState.highMemory t) (t.scratch + 8).toNat) h1.1 wc
  have sc : t.cell.toNat + 4 ≤ (InterfaceLazyState.wordMemory t).byteSize := by
    change t.cell.toNat + 4 ≤ (writeI32 (InterfaceLazyState.highMemory t) (t.cell + 12).toNat _).byteSize
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h2.2.1, h1.2.1, h0.2.1]; have hc := hr.cell; try dsimp only [t, tailLayout]
    omega
  have h3 := writeI32_spec (InterfaceLazyState.wordMemory t) t.cell.toNat 1 h2.1 sc
  have sh : ((t.scratch + 16) + 12).toNat + 4 ≤ (InterfaceLazyState.statusMemory t).byteSize := by
    change ((scratch p + 16) + 12).toNat + 4 ≤ (writeI32 (InterfaceLazyState.wordMemory t) t.cell.toNat 1).byteSize
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h3.2.1, h2.2.1, h1.2.1, h0.2.1, hs28]; have hb := hr.scratchSpan; omega
  have h4 := writeI32_spec (InterfaceLazyState.statusMemory t) ((t.scratch + 16) + 12).toNat
    (InterfaceLazyState.oldHigh t) h3.1 sh
  have ss : t.scratch.toNat + 20 ≤ (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t)).byteSize := by
    change t.scratch.toNat + 20 ≤ (writeI32 (InterfaceLazyState.statusMemory t) ((t.scratch + 16) + 12).toNat _).byteSize
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h4.2.1, h3.2.1, h2.2.1, h1.2.1, h0.2.1]; have hb := hr.scratchSpan; try dsimp only [t, tailLayout]
    omega
  have h5 := writeI32_spec (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t))
    (t.scratch.toNat + 16) (InterfaceLazyState.oldStatus t) h4.1 (by omega)
  have sl : t.scratch.toNat + 28 ≤ (InterfaceLazySaved.statusMemory (InterfaceLazyState.statusMemory t) t.scratch
      (InterfaceLazyState.oldStatus t) (InterfaceLazyState.oldHigh t)).byteSize := by
    change t.scratch.toNat + 28 ≤ (writeI32 (InterfaceLazySaved.highMemory (InterfaceLazyState.statusMemory t) t.scratch (InterfaceLazyState.oldHigh t))
      (t.scratch.toNat + 16) _).byteSize
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h5.2.1, h4.2.1, h3.2.1, h2.2.1, h1.2.1, h0.2.1]; have hb := hr.scratchSpan; try dsimp only [t, tailLayout]
    omega
  have r0 : readI32 t.memory p.cell.toNat = readI32 p.memory p.cell.toNat := by
    apply LoadedValueReturnData.readI32_frame
    intro i hi
    try dsimp only [t, tailLayout, InterfaceLazyState.highMemory, InterfaceLazyState.wordMemory, InterfaceLazyState.statusMemory, InterfaceLazySaved.highMemory, InterfaceLazySaved.statusMemory] at *
    rw [h0.2.2.2]
    have sep := hr.separated
    have hn : ¬((scratch p).toNat ≤ p.cell.toNat + i ∧ p.cell.toNat + i < (scratch p).toNat + 8) := by omega
    simp only [hn, ↓reduceIte]
  have r1 : readI32 (InterfaceLazyState.highMemory t) p.cell.toNat = readI32 t.memory p.cell.toNat := by
    apply LoadedValueReturnData.readI32_frame
    intro i hi
    change (writeI64 t.memory (t.cell.toNat + 4) (readI64 t.memory t.scratch.toNat)).read8 (p.cell.toNat + i) = t.memory.read8 (p.cell.toNat + i)
    rw [h1.2.2.2]
    have hn : ¬(t.cell.toNat + 4 ≤ p.cell.toNat + i ∧ p.cell.toNat + i < t.cell.toNat + 4 + 8) := by
      dsimp only [t, tailLayout]
      omega
    rw [ite_eq_right hn]
  have r2 : readI32 (InterfaceLazyState.wordMemory t) p.cell.toNat = readI32 (InterfaceLazyState.highMemory t) p.cell.toNat := by
    apply LoadedValueReturnData.readI32_frame
    intro i hi
    change (writeI32 (InterfaceLazyState.highMemory t) (t.cell + 12).toNat (readI32 (InterfaceLazyState.highMemory t) (t.scratch + 8).toNat)).read8 (p.cell.toNat + i) = (InterfaceLazyState.highMemory t).read8 (p.cell.toNat + i)
    rw [h2.2.2.2]
    have hn : ¬((t.cell + 12).toNat ≤ p.cell.toNat + i ∧ p.cell.toNat + i < (t.cell + 12).toNat + 4) := by
      change ¬((p.cell + 12).toNat ≤ p.cell.toNat + i ∧ p.cell.toNat + i < (p.cell + 12).toNat + 4)
      rw [hc12]; omega
    rw [ite_eq_right hn]
  refine ⟨hc, hs, wc, ws, sc, sh, ss, sl, ?_⟩
  change readI32 (InterfaceLazyState.wordMemory t) p.cell.toNat = 0
  rw [r2, r1, r0, hr.empty]

end WNear.Proofs.InterfaceLazyNative
