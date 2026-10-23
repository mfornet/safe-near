import WasmLogic.Rules.Table
import WasmLogic.Tactic

/-!
# Table and bulk-memory rules at work

Two small fragments, one per family of the rules in `Rules/Table.lean`, to
show that they compose with the rest: `memory.fill` then `memory.copy`
between two owned runs of bytes, and `table.set`, `table.get` and
`table.grow` on owned entries.
-/

namespace WasmLogic.Examples

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

section Proof

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits} {d : Nat}

/-- Fill bytes 8..11 with `0xAB`, then copy them to 16..19. -/
def fillCopy : List Instr :=
  [.i32_const 8, .i32_const 0xAB, .i32_const 4, .memory_fill,
    .i32_const 16, .i32_const 8, .i32_const 4, .memory_copy]

theorem fillCopy_spec (f : Frame) (n : Nat) (o₁ o₂ : List UInt8) (Φ : Post H GF)
    (hn : f.mi.memAddrs[0]? = some n) (h₁ : o₁.length = 4) (h₂ : o₂.length = 4) :
    n ↦[wms][ 8 ] o₁ ∗ n ↦[wms][ 16 ] o₂ ∗
      (n ↦[wms][ 8 ] List.replicate 4 0xAB ∗ n ↦[wms][ 16 ] List.replicate 4 0xAB -∗ Φ.normal [] f)
      ⊢ wpi lim d f [] fillCopy Φ := by
  iintro ⟨H₁, H₂, HΦ⟩
  have hne₁ : o₁ ≠ [] := fun h => by simp [h] at h₁
  have hne₂ : o₂ ≠ [] := fun h => by simp [h] at h₂
  simp only [fillCopy]
  wp_step 0 wpi_i32_const 8
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 0xAB
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 4
  inext; simp only [Post.seq_normal]
  wp_step 3 wpi_memory_fill n 8 0xAB 4 o₁ hn h₁ hne₁
  simp only [UInt32.reduceToNat]
  isplitl [H₁]
  · iexact H₁
  simp only [h₁]
  inext; iintro H₁; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 16
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 8
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 4
  inext; simp only [Post.seq_normal]
  wp_step 3 wpi_memory_copy n 16 8 4 o₂ (List.replicate 4 0xAB) hn h₂ (by simp) hne₂ (by decide)
  simp only [UInt32.reduceToNat]
  isplitl [H₂]
  · iexact H₂
  isplitl [H₁]
  · iexact H₁
  inext; iintro ⟨H₂, H₁⟩; simp only [Post.seq_normal]
  iapply wpi_nil
  iapply HΦ
  isplitl [H₁]
  · iexact H₁
  · iexact H₂

/-- Overwrite entry 2 of table 0 with a null reference, read it back, then
grow the table by one null entry. -/
def setGetGrow : List Instr :=
  [.i32_const 2, .ref_null .funcref, .table_set 0, .i32_const 2, .table_get 0, .i32_const 1,
    .table_grow 0]

theorem setGetGrow_spec (f : Frame) (ta size : Nat) (r : Ref) (Φ : Post H GF)
    (hta : f.mi.tableAddrs[0]? = some ta) (hsize : size + 1 ≤ 2 ^ 32 - 1) :
    ta ↦[wt][ 2 ] r ∗ tableInfoPt ta size .funcref none ∗
      (ta ↦[wt][ 2 ] .null .funcref ∗ tableInfoPt ta (size + 1) .funcref none ∗
          ta ↦[wts][ size ] [.null .funcref] -∗ Φ.normal [.i32 (UInt32.ofNat size)] f)
      ⊢ wpi lim d f [] setGetGrow Φ := by
  iintro ⟨He, Hi, HΦ⟩
  simp only [setGetGrow]
  wp_step 0 wpi_i32_const 2
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_ref_null .funcref
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_table_set 0 ta 2 r (.null .funcref) hta
  simp only [UInt32.reduceToNat]
  isplitl [He]
  · iexact He
  inext; iintro He; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 2
  inext; simp only [Post.seq_normal]
  wp_step 1 wpi_table_get 0 ta 2 (.null .funcref) hta
  simp only [UInt32.reduceToNat]
  isplitl [He]
  · iexact He
  inext; iintro He; simp only [Post.seq_normal]
  wp_step 0 wpi_i32_const 1
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_table_grow 0 ta size .funcref none (.null .funcref) 1 hta
    ⟨by simpa using hsize, fun _ h => by cases h⟩
  isplitl [Hi]
  · iexact Hi
  inext; iintro ⟨Hi, Hn⟩; simp only [Post.seq_normal, List.nil_append, UInt32.reduceToNat, List.replicate_one]
  iapply wpi_nil
  iapply HΦ
  isplitl [He]
  · iexact He
  isplitl [Hi]
  · iexact Hi
  · iexact Hn

end Proof

end WasmLogic.Examples
