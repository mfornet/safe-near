import Bridge.Functions.Add128

/-!
# 128-bit comparison and checked subtraction on two `i64` words

`a >= b` on `u128` compiles to `select(x1 == y1, x0 >=u y0, x1 >=u y1)`; `checked_sub` to
`d0 = x0 - y0`, `d1 = x1 - y1 - (x0 <u y0)` and the overflow flag
`select(d1 == x1, d0 >u x0, d1 >u x1)`.

* `ge128_flag`: the comparison is 1 exactly when `Y ≤ X` (`X = x0 + 2^64 x1`, `Y` likewise).
* `sub128_flag`: with `Y ≤ X`, the overflow flag is 0; `sub128_words`: `d0 + 2^64 d1 = X - Y`.
-/

namespace WNear.Binary.Cmp128

open Wasm

theorem ge128_flag (x0 x1 y0 y1 : UInt64) :
    (if Numeric.bool (Numeric.irelop64 IRelOp.eq x1 y1) = 0
      then Numeric.bool (Numeric.irelop64 IRelOp.ge_u x1 y1)
      else Numeric.bool (Numeric.irelop64 IRelOp.ge_u x0 y0)) =
    (if y0.toNat + 2 ^ 64 * y1.toNat ≤ x0.toNat + 2 ^ 64 * x1.toNat then 1 else 0) := by
  have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := y0.toNat_lt; have h3 := y1.toNat_lt
  by_cases he : x1 = y1
  · subst he
    have hdec : Numeric.bool (Numeric.irelop64 IRelOp.eq x1 x1) = 1 := by simp [Numeric.bool, Numeric.irelop64]
    rw [hdec, if_neg (by decide)]
    by_cases hl : y0.toNat ≤ x0.toNat
    · rw [if_pos (by omega)]; simp [Numeric.bool, Numeric.irelop64, UInt64.le_iff_toNat_le, hl]
    · rw [if_neg (by omega)]; simp [Numeric.bool, Numeric.irelop64, UInt64.le_iff_toNat_le, hl]
  · have hn : x1.toNat ≠ y1.toNat := fun h => he (UInt64.toNat_inj.mp h)
    have hdec : Numeric.bool (Numeric.irelop64 IRelOp.eq x1 y1) = 0 := by simp [Numeric.bool, Numeric.irelop64, he]
    rw [hdec, if_pos rfl]
    by_cases hl : y1.toNat ≤ x1.toNat
    · rw [if_pos (by omega)]; simp [Numeric.bool, Numeric.irelop64, UInt64.le_iff_toNat_le, hl]
    · rw [if_neg (by omega)]; simp [Numeric.bool, Numeric.irelop64, UInt64.le_iff_toNat_le, hl]

theorem borrow_val (x0 y0 : UInt64) :
    (Numeric.bool (Numeric.irelop64 IRelOp.lt_u x0 y0)).toUInt64.toNat = if x0.toNat < y0.toNat then 1 else 0 := by
  by_cases h : x0.toNat < y0.toNat <;> simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt, h]

theorem sub128_words (x0 x1 y0 y1 : UInt64)
    (hle : y0.toNat + 2 ^ 64 * y1.toNat ≤ x0.toNat + 2 ^ 64 * x1.toNat) :
    (x0 - y0).toNat + 2 ^ 64 * (x1 - y1 - (Numeric.bool (Numeric.irelop64 IRelOp.lt_u x0 y0)).toUInt64).toNat =
      (x0.toNat + 2 ^ 64 * x1.toNat) - (y0.toNat + 2 ^ 64 * y1.toNat) := by
  have hb := borrow_val x0 y0
  generalize (Numeric.bool (Numeric.irelop64 IRelOp.lt_u x0 y0)).toUInt64 = b at hb ⊢
  have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := y0.toNat_lt; have h3 := y1.toNat_lt
  rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_sub, hb]
  generalize x0.toNat = a at *
  generalize x1.toNat = c at *
  generalize y0.toNat = a' at *
  generalize y1.toNat = c' at *
  by_cases h : a < a'
  · rw [if_pos h] at *; omega
  · rw [if_neg h] at *; omega

theorem sub128_flag (x0 x1 y0 y1 : UInt64)
    (hle : y0.toNat + 2 ^ 64 * y1.toNat ≤ x0.toNat + 2 ^ 64 * x1.toNat) :
    (if Numeric.bool (Numeric.irelop64 IRelOp.eq
          (x1 - y1 - (Numeric.bool (Numeric.irelop64 IRelOp.lt_u x0 y0)).toUInt64) x1) = 0
      then Numeric.bool (Numeric.irelop64 IRelOp.gt_u
          (x1 - y1 - (Numeric.bool (Numeric.irelop64 IRelOp.lt_u x0 y0)).toUInt64) x1)
      else Numeric.bool (Numeric.irelop64 IRelOp.gt_u (x0 - y0) x0)) = 0 := by
  have hb := borrow_val x0 y0
  generalize (Numeric.bool (Numeric.irelop64 IRelOp.lt_u x0 y0)).toUInt64 = b at hb ⊢
  have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := y0.toNat_lt; have h3 := y1.toNat_lt
  have hD : (x1 - y1 - b).toNat = x1.toNat - y1.toNat - (if x0.toNat < y0.toNat then 1 else 0) := by
    rw [UInt64.toNat_sub, UInt64.toNat_sub, hb]
    by_cases h : x0.toNat < y0.toNat
    · rw [if_pos h] at *; omega
    · rw [if_neg h] at *; omega
  by_cases he : x1 - y1 - b = x1
  · have hdec : Numeric.bool (Numeric.irelop64 IRelOp.eq (x1 - y1 - b) x1) = 1 := by
      simp [Numeric.bool, Numeric.irelop64, he]
    rw [hdec, if_neg (by decide)]
    have hn : (x1 - y1 - b).toNat = x1.toNat := by rw [he]
    have hl : ¬ (x0 - y0).toNat > x0.toNat := by
      rw [UInt64.toNat_sub]
      by_cases h : x0.toNat < y0.toNat
      · rw [if_pos h] at hD; omega
      · omega
    simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt, hl]
  · have hdec : Numeric.bool (Numeric.irelop64 IRelOp.eq (x1 - y1 - b) x1) = 0 := by
      simp [Numeric.bool, Numeric.irelop64, he]
    rw [hdec, if_pos rfl]
    have hn : (x1 - y1 - b).toNat ≠ x1.toNat := fun h => he (UInt64.toNat_inj.mp h)
    have hl : ¬ (x1 - y1 - b).toNat > x1.toNat := by
      by_cases h : x0.toNat < y0.toNat
      · rw [if_pos h] at hD; omega
      · rw [if_neg h] at hD; omega
    simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt, hl]

end WNear.Binary.Cmp128
