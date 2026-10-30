import Bridge.Functions.FmtU128Div

/-!
# 128-bit checked addition on two `i64` words

`u128::checked_add` compiles to `s0 = x0 + y0`, `c = s0 <u x0`, `s1 = x1 + y1 + c` and the overflow
flag `select(c, s1 <u x1, s1 == x1)`.

* `add128_flag`: the flag is 0 exactly when `X + Y < 2^128` (`X = x0 + 2^64 x1`, `Y` likewise).
* `add128_words`: `s0 + 2^64 s1 = (X + Y) mod 2^128`.
-/

namespace WNear.Binary.Add128

open Wasm

theorem bool_toUInt64 (b : Bool) : (Numeric.bool b).toUInt64.toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- The carry of the low words. -/
theorem carry_val (x0 y0 : UInt64) :
    (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0)).toUInt64.toNat = (x0.toNat + y0.toNat) / 2 ^ 64 :=
  FmtU128Div.carry64 x0 y0

theorem add128_words (x0 x1 y0 y1 : UInt64) :
    (x0 + y0).toNat + 2 ^ 64 * (x1 + y1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0)).toUInt64).toNat =
      (x0.toNat + 2 ^ 64 * x1.toNat + (y0.toNat + 2 ^ 64 * y1.toNat)) % 2 ^ 128 := by
  have hc := carry_val x0 y0
  generalize (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0)).toUInt64 = c at hc ⊢
  have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := y0.toNat_lt; have h3 := y1.toNat_lt
  simp only [UInt64.toNat_add, hc]
  generalize x0.toNat = a at *
  generalize x1.toNat = b at *
  generalize y0.toNat = a' at *
  generalize y1.toNat = b' at *
  have hcc : (a + a') / 2 ^ 64 ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcc with hz | hz <;> rw [hz] <;> omega

theorem add128_flag (x0 x1 y0 y1 : UInt64) :
    (if Numeric.bool (Numeric.irelop64 IRelOp.eq
          (x1 + y1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0)).toUInt64) x1) = 0
      then Numeric.bool (Numeric.irelop64 IRelOp.lt_u
          (x1 + y1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0)).toUInt64) x1)
      else Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0)) =
    (if x0.toNat + 2 ^ 64 * x1.toNat + (y0.toNat + 2 ^ 64 * y1.toNat) < 2 ^ 128 then 0 else 1) := by
  have hc := carry_val x0 y0
  have h0 := x0.toNat_lt; have h1 := x1.toNat_lt; have h2 := y0.toNat_lt; have h3 := y1.toNat_lt
  generalize hcb : Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x0 + y0) x0) = cb at hc ⊢
  have hcb01 : cb = 0 ∨ cb = 1 := by rw [← hcb]; unfold Numeric.bool; split <;> simp
  generalize hS : x1 + y1 + cb.toUInt64 = S
  have hSn : S.toNat = (x1.toNat + y1.toNat + (x0.toNat + y0.toNat) / 2 ^ 64) % 2 ^ 64 := by
    rw [← hS, UInt64.toNat_add, UInt64.toNat_add, hc]; omega
  have hcn : cb.toNat = (x0.toNat + y0.toNat) / 2 ^ 64 := by
    rcases hcb01 with rfl | rfl <;> simp at hc ⊢ <;> omega
  have hX : x0.toNat + 2 ^ 64 * x1.toNat + (y0.toNat + 2 ^ 64 * y1.toNat) < 2 ^ 128 ↔
      x1.toNat + y1.toNat + (x0.toNat + y0.toNat) / 2 ^ 64 < 2 ^ 64 := by omega
  rw [if_congr hX rfl rfl]
  by_cases he : S = x1
  · have hn : S.toNat = x1.toNat := by rw [he]
    have hdec : Numeric.bool (Numeric.irelop64 IRelOp.eq S x1) = 1 := by
      simp [Numeric.bool, Numeric.irelop64, he]
    rw [hdec, if_neg (by decide)]
    rcases hcb01 with rfl | rfl
    · simp at hcn; rw [if_pos (by omega)]
    · simp at hcn; rw [if_neg (by omega)]
  · have hn : S.toNat ≠ x1.toNat := fun h => he (UInt64.toNat_inj.mp h)
    have hdec : Numeric.bool (Numeric.irelop64 IRelOp.eq S x1) = 0 := by
      simp [Numeric.bool, Numeric.irelop64, he]
    rw [hdec, if_pos rfl]
    by_cases hl : S.toNat < x1.toNat
    · have hl' : Numeric.bool (Numeric.irelop64 IRelOp.lt_u S x1) = 1 := by
        simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt, hl]
      rw [hl', if_neg (by omega)]
    · have hl' : Numeric.bool (Numeric.irelop64 IRelOp.lt_u S x1) = 0 := by
        simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt, hl]
      rw [hl', if_pos (by omega)]

end WNear.Binary.Add128
