import Proofs.SerializeMultiplyArithmetic

/-! Kernel arithmetic for the carries used by the actual general f954 product. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic

theorem carry_toNat (x y : UInt64) : (carry x y).toNat = if x.toNat < y.toNat then 1 else 0 := by
  unfold carry Numeric.irelop64 Numeric.bool
  by_cases h : x < y
  · simp [h,UInt64.lt_iff_toNat_lt.mp h]
  · simp [h,show ¬x.toNat < y.toNat from fun hn => h (UInt64.lt_iff_toNat_lt.mpr hn)]

theorem carry_sum (x y : UInt64) :
    (x+y).toNat+(carry (x+y) x).toNat*2^64=x.toNat+y.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  rw [carry_toNat,UInt64.toNat_add]
  simp only [Nat.reducePow]
  split <;> omega

/-- The wrapped sum's upper limb and its overflow bit reconstruct the full upper sum. -/
theorem carry_join (x y : UInt64) :
    ((carry (x+y) x <<< (32 : UInt64)) ||| ((x+y) >>> (32 : UInt64))).toNat =
      (x.toNat+y.toNat)/2^32 := by
  have sum := carry_sum x y
  have carryBound : (carry (x+y) x).toNat < 2 := by rw [carry_toNat]; split <;> decide
  have wrapped := (x+y).toNat_lt
  have upperBound : (x+y).toNat/2^32 < 2^32 := by omega
  rw [UInt64.toNat_or,UInt64.toNat_shiftLeft,UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_ofNat,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show (carry (x+y) x).toNat*2^32 < 2^64 by omega)]
  change (carry (x+y) x).toNat*2^32 ||| (x+y).toNat/2^32=(x.toNat+y.toNat)/2^32
  rw [Nat.mul_comm (carry (x+y) x).toNat (2^32)]
  rw [←Nat.two_pow_add_eq_or_of_lt upperBound (carry (x+y) x).toNat]
  omega

/-- The second carry is exactly the overflow of the low-word addition. -/
theorem lowWord_carry (w : Words) :
    (lowWord w).toNat+(carry (lowWord w) (shifted w)).toNat*2^64 =
      (shifted w).toNat+(b0 w*a0 w).toNat := by
  exact carry_sum (shifted w) (b0 w*a0 w)

/-- Exact natural formula for the implemented high word, with both carry effects explicit.
The products inside `.toNat` retain the actual wrapping-word semantics. -/
theorem highWord_toNat (w : Words) :
    (highWord w).toNat =
      (((cross0 w).toNat+(b1 w*a0 w).toNat)/2^32+(b1 w*a1 w).toNat+
        (carry (lowWord w) (shifted w)).toNat+(w.bHi*w.aLo+w.bLo*w.aHi).toNat)%2^64 := by
  have upper := carry_join (cross0 w) (b1 w*a0 w)
  change ((carry (cross w) (cross0 w) <<< (32 : UInt64)) ||| (cross w >>> (32 : UInt64))).toNat = _ at upper
  unfold highWord
  simp only [UInt64.toNat_add]
  rw [upper]
  simp only [Nat.add_mod,Nat.mod_mod]

end WNear.Proofs.SerializeMultiply
