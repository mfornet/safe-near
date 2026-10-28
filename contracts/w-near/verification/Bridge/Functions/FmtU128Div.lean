import Bridge.Functions.FmtDigits
import Wasm.Numeric

/-!
# The arithmetic of `core::fmt::num::fmt_u128` (function 902)

`fmt_u128(lo, hi, is_nonnegative, f)` formats `n = lo + 2^64 hi` by splitting
off 19 digits at a time with `udiv_1e19`:

* **fast path** (`hi ≤ 524287`, `n < 2^83`): `n / 10^19 = ((n >> 19) as u64) / 5^19`
  (`udiv_fast`);
* **slow path**: `n / 10^19 = u128_mulhi(n, magic) >> 62`, `magic = ⌊2^190 / 10^19⌋ + 1`
  (`magic_div`: the error `magic · 10^19 - 2^190 < 2^62` is small enough for every
  `n < 2^128`), the high half computed from four `__multi3` (954) products with
  explicit carries (`mulhi_words`), shifted by 62 (`shr62_words`);
* **the remainder**: `lo + low64(q · (2^128 - 10^19))` (a fifth `__multi3`,
  `rem_words`), which only depends on `q mod 2^64`; the second round (on `q`,
  `q < 2^65`, always the fast path) reuses it with garbage in the high word.

`parse_u64_into` (900) writes each remainder's digits; `memset` (952) pads with
`'0'` up to the 19-digit boundary; a third quotient (`< 10`) is one digit.
`u128_digits` says the 39-byte buffer's tail is `decDigits n`
(`padDigits_eq_zeros`: the last `k` digits are zeros then `decDigits`).
-/

namespace WNear.Binary.FmtU128Div

open Wasm WNear.Binary.FmtDigits

/-- The magic multiplier of `udiv_1e19`: `⌊2^190 / 10^19⌋ + 1`. -/
def magic : Nat := 8507059173023461586 * 2 ^ 64 + 10779635027931437427

theorem magic_div (n : Nat) (hn : n < 2 ^ 128) : n * magic / 2 ^ 190 = n / 10 ^ 19 := by
  have hd : (0:Nat) < 10 ^ 19 := by norm_num
  have hM : 10 ^ 19 * magic = 2 ^ 190 + 4411138883991371776 := by norm_num [magic]
  set q := n / 10 ^ 19 with hq
  set r := n % 10 ^ 19 with hr
  have hnq : n = 10 ^ 19 * q + r := (Nat.div_add_mod n _).symm
  have hr' : r ≤ 10 ^ 19 - 1 := by have := Nat.mod_lt n hd; omega
  have hq' : q ≤ (2 ^ 128 - 1) / 10 ^ 19 := Nat.div_le_div_right (by omega)
  have key : n * magic = q * 2 ^ 190 + (q * 4411138883991371776 + r * magic) := by
    rw [hnq, Nat.add_mul, Nat.mul_comm (10 ^ 19) q, Nat.mul_assoc, hM]; ring
  have b1 : q * 4411138883991371776 ≤ (2 ^ 128 - 1) / 10 ^ 19 * 4411138883991371776 :=
    Nat.mul_le_mul_right _ hq'
  have b2 : r * magic ≤ (10 ^ 19 - 1) * magic := Nat.mul_le_mul_right _ hr'
  have b3 : (2 ^ 128 - 1) / 10 ^ 19 * 4411138883991371776 + (10 ^ 19 - 1) * magic < 2 ^ 190 := by
    norm_num [magic]
  rw [key, Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.add_le_add b1 b2) b3)]
  simp

theorem b2u (b : Bool) : (if b then (1 : UInt64) else 0).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- The fast path of `udiv_1e19`: `hi < 2^19`, so `n >> 19` fits a `u64`. -/
theorem udiv_fast (lo hi : UInt64) (h : hi.toNat ≤ 524287) :
    (((lo >>> 19) ||| (hi <<< 45)) / 19073486328125).toNat = (lo.toNat + 2 ^ 64 * hi.toNat) / 10 ^ 19 := by
  have hl := lo.toNat_lt
  have e1 : ((lo >>> 19) ||| (hi <<< 45)).toNat = (lo.toNat + 2 ^ 64 * hi.toNat) / 2 ^ 19 := by
    rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, UInt64.reduceToNat, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
    omega
  rw [UInt64.toNat_div, e1, Nat.div_div_eq_div_mul]
  norm_num


theorem carry64 (x y : UInt64) :
    (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x + y) x)).toUInt64.toNat = (x.toNat + y.toNat) / 2 ^ 64 := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  by_cases h : x + y < x
  · simp only [Numeric.bool, Numeric.irelop64, h, decide_true, ite_true]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp; omega
  · simp only [Numeric.bool, Numeric.irelop64, h, decide_false]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp; omega


/-- `u128_mulhi(n, magic)` as 902 computes it from the four `__multi3` products. -/
theorem mulhi_words (lo hi a0 a1 b0 b1 c0 c1 d0 d1 : UInt64)
    (ha : a0.toNat + 2 ^ 64 * a1.toNat = lo.toNat * 10779635027931437427)
    (hb : b0.toNat + 2 ^ 64 * b1.toNat = lo.toNat * 8507059173023461586)
    (hc : c0.toNat + 2 ^ 64 * c1.toNat = hi.toNat * 10779635027931437427)
    (hd : d0.toNat + 2 ^ 64 * d1.toNat = hi.toNat * 8507059173023461586) :
    let l1 := a1 + b0
    let l6 := b1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u l1 a1)).toUInt64
    let l5 := l6 + d0
    let t := l1 + c0
    let L := l5 + (c1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u t l1)).toUInt64)
    let H := d1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u l5 l6)).toUInt64 +
      (Numeric.bool (Numeric.irelop64 IRelOp.lt_u L l5)).toUInt64
    L.toNat + 2 ^ 64 * H.toNat = (lo.toNat + 2 ^ 64 * hi.toNat) * magic / 2 ^ 128 := by
  intro l1 l6 l5 t L H
  have hlo := lo.toNat_lt; have hhi := hi.toNat_lt
  have := a0.toNat_lt; have := a1.toNat_lt; have := b0.toNat_lt; have := b1.toNat_lt
  have := c0.toNat_lt; have := c1.toNat_lt; have := d0.toNat_lt; have := d1.toNat_lt
  have e1 : (Numeric.bool (Numeric.irelop64 IRelOp.lt_u l1 a1)).toUInt64.toNat =
      (a1.toNat + b0.toNat) / 2 ^ 64 := carry64 a1 b0
  have e2 : (Numeric.bool (Numeric.irelop64 IRelOp.lt_u l5 l6)).toUInt64.toNat =
      (l6.toNat + d0.toNat) / 2 ^ 64 := carry64 l6 d0
  have e3 : (Numeric.bool (Numeric.irelop64 IRelOp.lt_u t l1)).toUInt64.toNat =
      (l1.toNat + c0.toNat) / 2 ^ 64 := carry64 l1 c0
  have e4 : (Numeric.bool (Numeric.irelop64 IRelOp.lt_u L l5)).toUInt64.toNat =
      (l5.toNat + (c1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u t l1)).toUInt64).toNat) / 2 ^ 64 :=
    carry64 l5 _
  have hl1 : l1.toNat = (a1.toNat + b0.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  have hl6 : l6.toNat = (b1.toNat + (a1.toNat + b0.toNat) / 2 ^ 64) % 2 ^ 64 := by
    simp only [l6, UInt64.toNat_add, e1]
  have hl5 : l5.toNat = (l6.toNat + d0.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  have hh2 : (c1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u t l1)).toUInt64).toNat =
      (c1.toNat + (l1.toNat + c0.toNat) / 2 ^ 64) % 2 ^ 64 := by
    rw [UInt64.toNat_add, e3]
  have hL : L.toNat = (l5.toNat + (c1.toNat + (l1.toNat + c0.toNat) / 2 ^ 64) % 2 ^ 64) % 2 ^ 64 := by
    simp only [L, UInt64.toNat_add, hh2]
  have hH : H.toNat = (d1.toNat + (l6.toNat + d0.toNat) / 2 ^ 64 +
      (l5.toNat + (c1.toNat + (l1.toNat + c0.toNat) / 2 ^ 64) % 2 ^ 64) / 2 ^ 64) % 2 ^ 64 := by
    simp only [H, UInt64.toNat_add, e2, e4, hh2]; omega
  have hM : (lo.toNat + 2 ^ 64 * hi.toNat) * magic =
      (a0.toNat + 2 ^ 64 * a1.toNat) + 2 ^ 64 * ((b0.toNat + 2 ^ 64 * b1.toNat) +
        (c0.toNat + 2 ^ 64 * c1.toNat)) + 2 ^ 128 * (d0.toNat + 2 ^ 64 * d1.toNat) := by
    rw [ha, hb, hc, hd, magic]; ring
  -- the steps of the schoolbook product
  have hb1 : b1.toNat + (a1.toNat + b0.toNat) / 2 ^ 64 < 2 ^ 64 := by omega
  have hm : lo.toNat * 8507059173023461586 + a1.toNat = l1.toNat + 2 ^ 64 * l6.toNat := by
    rw [hl1, hl6, Nat.mod_eq_of_lt hb1]; omega
  have hc1 : c1.toNat + (l1.toNat + c0.toNat) / 2 ^ 64 < 2 ^ 64 := by omega
  have hT : (lo.toNat + 2 ^ 64 * hi.toNat) * magic / 2 ^ 128 =
      d0.toNat + 2 ^ 64 * d1.toNat + l6.toNat + c1.toNat + (l1.toNat + c0.toNat) / 2 ^ 64 := by
    rw [hM]; omega
  have hTb : (lo.toNat + 2 ^ 64 * hi.toNat) * magic / 2 ^ 128 < 2 ^ 128 := by
    apply Nat.div_lt_of_lt_mul
    have : (lo.toNat + 2 ^ 64 * hi.toNat) < 2 ^ 128 := by omega
    calc (lo.toNat + 2 ^ 64 * hi.toNat) * magic < 2 ^ 128 * magic :=
          Nat.mul_lt_mul_of_pos_right this (by norm_num [magic])
      _ ≤ 2 ^ 128 * 2 ^ 128 := Nat.mul_le_mul_left _ (by norm_num [magic])
  rw [hT] at hTb ⊢
  rw [hL, hH, hl5, Nat.mod_eq_of_lt hc1]
  omega

/-- The quotient's words: `(L + 2^64 H) >> 62`. -/
theorem shr62_words (L H : UInt64) :
    ((L >>> 62) ||| (H <<< 2)).toNat + 2 ^ 64 * (H >>> 62).toNat = (L.toNat + 2 ^ 64 * H.toNat) / 2 ^ 62 := by
  have hL := L.toNat_lt; have hH := H.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, UInt64.reduceToNat, Nat.reduceMod]
  have h1 : L.toNat / 2 ^ 62 < 2 ^ 2 := by omega
  rw [Nat.or_comm, show H.toNat * 2 ^ 2 % 2 ^ 64 = 2 ^ 2 * (H.toNat % 2 ^ 62) by omega,
    ← Nat.two_pow_add_eq_or_of_lt h1]
  omega

/-- The remainder: the low word of `y · (2^128 - 10^19)` plus `x ≡ N`, for `y ≡ N / 10^19`
(mod `2^64`). -/
theorem rem_words (r0 r1 y z x : UInt64) (N : Nat)
    (hr : r0.toNat + 2 ^ 64 * r1.toNat =
      (y.toNat + 2 ^ 64 * z.toNat) * (8446744073709551616 + 2 ^ 64 * 18446744073709551615) % 2 ^ 128)
    (hx : x.toNat = N % 2 ^ 64) (hy : y.toNat = N / 10 ^ 19 % 2 ^ 64) :
    (r0 + x).toNat = N % 10 ^ 19 := by
  have := r0.toNat_lt; have := r1.toNat_lt; have := z.toNat_lt
  rw [UInt64.toNat_add, hx]
  omega

theorem padDigits_zero (k : Nat) : padDigits k 0 = List.replicate k (digit 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padDigits, Nat.zero_div, ih, Nat.zero_mod, List.replicate_succ']

/-- The last `k` digits of `m < 10^k`: zeros, then `decDigits m`. -/
theorem padDigits_eq_zeros (k m : Nat) (hk : 1 ≤ k) (hm : m < 10 ^ k) :
    padDigits k m = List.replicate (k - (decDigits m).length) (digit 0) ++ decDigits m := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
    rw [padDigits]
    by_cases h10 : m < 10
    · rw [Nat.div_eq_of_lt h10, padDigits_zero, decDigits_lt10 m h10, Nat.mod_eq_of_lt h10]
      simp
    · have hq : m / 10 < 10 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [Nat.pow_succ] at hm; exact hm
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at hm; omega
        · omega
      rw [ih (m / 10) hk1 hq, decDigits.eq_1 m]
      simp only [h10, ↓reduceIte, List.length_append, List.length_singleton, List.append_assoc]
      congr 2
      omega

/-- The digits `fmt_u128` assembles: `n = q·10^19 + r`, `q = q2·10^19 + r2`. -/
theorem u128_digits (n : Nat) (hn : n < 2 ^ 128) :
    decDigits n =
      if n / 10 ^ 19 = 0 then decDigits (n % 10 ^ 19)
      else if n / 10 ^ 19 / 10 ^ 19 = 0 then
        decDigits (n / 10 ^ 19 % 10 ^ 19) ++
          List.replicate (19 - (decDigits (n % 10 ^ 19)).length) (digit 0) ++ decDigits (n % 10 ^ 19)
      else
        [digit (n / 10 ^ 19 / 10 ^ 19)] ++
          List.replicate (19 - (decDigits (n / 10 ^ 19 % 10 ^ 19)).length) (digit 0) ++
          decDigits (n / 10 ^ 19 % 10 ^ 19) ++
          List.replicate (19 - (decDigits (n % 10 ^ 19)).length) (digit 0) ++ decDigits (n % 10 ^ 19) := by
  have hr := padDigits_eq_zeros 19 (n % 10 ^ 19) (by norm_num) (Nat.mod_lt _ (by norm_num))
  have hr2 := padDigits_eq_zeros 19 (n / 10 ^ 19 % 10 ^ 19) (by norm_num) (Nat.mod_lt _ (by norm_num))
  split
  · rename_i h; rw [Nat.mod_eq_of_lt (by omega)]
  split
  · rename_i h1 h2
    rw [decDigits_split 19 n (by omega), Nat.mod_eq_of_lt (a := n / 10 ^ 19) (by omega),
      ← padDigits_mod 19 n, hr, List.append_assoc]
  · rename_i h1 h2
    have hq2 : n / 10 ^ 19 / 10 ^ 19 < 10 := by
      rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by norm_num)]; omega
    rw [decDigits_split 19 n (by omega), decDigits_split 19 (n / 10 ^ 19) (by omega),
      decDigits_lt10 _ hq2, ← padDigits_mod 19 n, ← padDigits_mod 19 (n / 10 ^ 19), hr, hr2]
    simp only [List.append_assoc, List.cons_append]

end WNear.Binary.FmtU128Div
