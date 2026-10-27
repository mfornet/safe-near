import Proofs.SerializeMultiplyProduct
import Proofs.SerializeMultiplyFrame

/-! General natural-number correctness of the actual f954 two-word product. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

private theorem mask32_toNat (x : UInt64) :
    (x &&& 4294967295).toNat = x.toNat % 2^32 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32

private theorem upper32_toNat (x : UInt64) :
    (x >>> (32 : UInt64)).toNat = x.toNat / 2^32 := by
  rw [UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_ofNat,Nat.shiftRight_eq_div_pow]

private theorem limb_mul (x y : UInt64) (hx : x.toNat < 2^32) (hy : y.toNat < 2^32) :
    (x*y).toNat=x.toNat*y.toNat := by
  have h := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (show 0 < 2^32 by decide)
  rw [UInt64.toNat_mul,Nat.mod_eq_of_lt (by exact h)]

private theorem limbs (w : Words) :
    (a0 w).toNat < 2^32 ∧ (a1 w).toNat < 2^32 ∧
    (b0 w).toNat < 2^32 ∧ (b1 w).toNat < 2^32 := by
  have ha := w.aLo.toNat_lt
  have hb := w.bLo.toNat_lt
  simp only [a0,a1,b0,b1,mask32_toNat,upper32_toNat]
  omega

private theorem split_nat (x : UInt64) :
    x.toNat = (x &&& 4294967295).toNat + (x >>> (32 : UInt64)).toNat*2^32 := by
  rw [mask32_toNat,upper32_toNat]
  omega

private theorem shifted_toNat (w : Words) :
    (shifted w).toNat = ((cross0 w).toNat+(b1 w*a0 w).toNat)%2^32*2^32 := by
  simp only [shifted,UInt64.toNat_shiftLeft,UInt64.toNat_ofNat,Nat.shiftLeft_eq,cross,UInt64.toNat_add]
  change (((cross0 w).toNat+(b1 w*a0 w).toNat)%(2^32*2^32)*2^32)%(2^32*2^32)=_
  rw [Nat.mul_mod_mul_right,Nat.mod_mul_right_mod]

/-- The implemented low product and its unbounded high part reconstruct the full 64x64 product. -/
theorem low_product_exact (w : Words) :
    (lowWord w).toNat + 2^64 *
      (((cross0 w).toNat+(b1 w*a0 w).toNat)/2^32+(b1 w*a1 w).toNat+
        (carry (lowWord w) (shifted w)).toNat) = w.aLo.toNat*w.bLo.toNat := by
  have hs := shifted_toNat w
  have hc := lowWord_carry w
  have ha := split_nat w.aLo
  have hb := split_nat w.bLo
  have hl := limbs w
  have m00 := limb_mul (b0 w) (a0 w) hl.2.2.1 hl.1
  have m01 := limb_mul (b0 w) (a1 w) hl.2.2.1 hl.2.1
  have m10 := limb_mul (b1 w) (a0 w) hl.2.2.2 hl.1
  have m11 := limb_mul (b1 w) (a1 w) hl.2.2.2 hl.2.1
  have hd := Nat.mod_add_div ((cross0 w).toNat+(b1 w*a0 w).toNat) (2^32)
  have hd' := congrArg (fun n => n*2^32) hd
  simp only [Nat.add_mul,Nat.mul_assoc] at hd'
  change w.aLo.toNat=(a0 w).toNat+(a1 w).toNat*2^32 at ha
  change w.bLo.toNat=(b0 w).toNat+(b1 w).toNat*2^32 at hb
  rw [ha,hb]
  rw [show (cross0 w).toNat=(b0 w).toNat*(a1 w).toNat from m01] at hs hd' ⊢
  rw [m00] at hc
  rw [m10] at hs hd' ⊢
  rw [m11]
  have poly : ((a0 w).toNat*(b0 w).toNat+(a0 w).toNat*((b1 w).toNat*2^32))+
      ((a1 w).toNat*(2^32*(b0 w).toNat)+(a1 w).toNat*(2^32*((b1 w).toNat*2^32))) =
      (b0 w).toNat*(a0 w).toNat+((b0 w).toNat*(a1 w).toNat+(b1 w).toNat*(a0 w).toNat)*2^32+
      ((b1 w).toNat*(a1 w).toNat)*2^64 := by
    simp only [Nat.add_mul,Nat.mul_assoc]
    ac_rfl
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  have poly' := poly
  simp only [Nat.add_mul,Nat.mul_assoc] at poly'
  omega

attribute [local irreducible] lowWord highWord cross cross0 shifted a0 a1 b0 b1 carry

private theorem packed_mod (low high : Nat) (hl : low < 2^64) :
    (low+2^64*high)%2^128=low+2^64*(high%2^64) := by
  change (low+2^64*high)%(2^64*2^64)=_
  rw [Nat.add_mod,Nat.mul_mod_mul_left]
  have hr := Nat.mod_lt high (show 0<2^64 by decide)
  rw [Nat.mod_eq_of_lt (show low < 2^64*2^64 by omega)]
  apply Nat.mod_eq_of_lt
  omega

/-- The actual f954 result is the product of both general 128-bit inputs modulo 2^128. -/
theorem product_correct (w : Words) :
    (lowWord w).toNat+2^64*(highWord w).toNat =
      ((w.aLo.toNat+2^64*w.aHi.toNat)*(w.bLo.toNat+2^64*w.bHi.toNat))%2^128 := by
  let upper := ((cross0 w).toNat+(b1 w*a0 w).toNat)/2^32+(b1 w*a1 w).toNat+
        (carry (lowWord w) (shifted w)).toNat
  let mixed := w.bHi.toNat*w.aLo.toNat+w.bLo.toNat*w.aHi.toNat
  have low : (lowWord w).toNat+2^64*upper=w.aLo.toNat*w.bLo.toNat := low_product_exact w
  have high : (highWord w).toNat=(upper+mixed)%2^64 := by
    rw [highWord_toNat]
    simp only [upper,mixed,UInt64.toNat_add,UInt64.toNat_mul,Nat.add_mod,Nat.mod_mod]
  have poly : (w.aLo.toNat+2^64*w.aHi.toNat)*(w.bLo.toNat+2^64*w.bHi.toNat) =
      (lowWord w).toNat+2^64*(upper+mixed)+2^128*(w.aHi.toNat*w.bHi.toNat) := by
    calc
      _ = w.aLo.toNat*w.bLo.toNat+2^64*mixed+2^128*(w.aHi.toNat*w.bHi.toNat) := by
        simp only [mixed,Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
        ac_rfl
      _ = _ := by
        have lifted := congrArg (fun n => n+2^64*mixed+2^128*(w.aHi.toNat*w.bHi.toNat)) low.symm
        exact lifted.trans (by simp only [Nat.mul_add];ac_rfl)
  rw [poly,Nat.add_mul_mod_self_left,packed_mod _ _ (lowWord w).toNat_lt,high]

/-- Reading the two actual stored words yields the mathematical 128-bit product. -/
theorem finalMemory_product (memory : Memory) (w : Words)
    (hw : memory.wf) (hb : w.out.toNat+16 ≤ memory.byteSize) :
    (readI64 (finalMemory memory w) w.out.toNat).toNat+
      2^64*(readI64 (finalMemory memory w) (w.out.toNat+8)).toNat =
      ((w.aLo.toNat+2^64*w.aHi.toNat)*(w.bLo.toNat+2^64*w.bHi.toNat))%2^128 := by
  have h := finalMemory_spec memory w hw hb
  rw [h.2.2.2.1,h.2.2.2.2.1]
  exact product_correct w

/-- The concrete normal-call poststore contains that product, under the original memory bounds. -/
theorem callAfter_product (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words)
    (hm : s.mems[index]?=some memory) (hw : memory.wf) (hb : w.out.toNat+16 ≤ memory.byteSize) :
    ∃ result, (callAfter s op index memory w).mems[index]?=some result ∧ result.wf ∧
      (readI64 result w.out.toNat).toNat+2^64*(readI64 result (w.out.toNat+8)).toNat =
        ((w.aLo.toNat+2^64*w.aHi.toNat)*(w.bLo.toNat+2^64*w.bHi.toNat))%2^128 := by
  exact ⟨finalMemory memory w,callAfter_memory s op index memory w hm,
    (finalMemory_spec memory w hw hb).1,finalMemory_product memory w hw hb⟩

end WNear.Proofs.SerializeMultiply
