import Proofs.SerializeMultiplyState

/-! Kernel arithmetic for the low word of the deployed multiplication helper. -/
namespace WNear.Proofs.SerializeMultiply
set_option maxRecDepth 16384

theorem shift32_eq_mul (x : UInt64) : x <<< (32 : UInt64) = x*4294967296 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_shiftLeft,UInt64.toNat_mul,Nat.shiftLeft_eq]

theorem split32_eq (x : UInt64) : x = (x &&& 4294967295)+(x >>> (32 : UInt64))*4294967296 := by
  have mask : (x &&& 4294967295).toNat = x.toNat % 4294967296 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add,UInt64.toNat_mul,mask,UInt64.toNat_shiftRight,Nat.shiftRight_eq_div_pow]
  change x.toNat = (x.toNat % 4294967296+(x.toNat/4294967296*4294967296)%18446744073709551616)%18446744073709551616
  have h := x.toBitVec.isLt
  change x.toNat < 18446744073709551616 at h
  omega

private theorem upper_product_zero (a b : UInt64) : (a*4294967296)*(b*4294967296)=0 := by
  calc
    _ = (a*b)*((4294967296 : UInt64)*4294967296) := by ac_rfl
    _ = 0 := by rw [show (4294967296 : UInt64)*4294967296=0 by decide,UInt64.mul_zero]

theorem lowWord_eq_mul (w : Words) : lowWord w = w.aLo*w.bLo := by
  have ha : w.aLo = a0 w+a1 w*4294967296 := split32_eq w.aLo
  have hb : w.bLo = b0 w+b1 w*4294967296 := split32_eq w.bLo
  calc
    lowWord w = (b0 w*a1 w+b1 w*a0 w)*4294967296+b0 w*a0 w := by
      simp only [lowWord,shifted,cross,cross0,shift32_eq_mul]
    _ = (a0 w+a1 w*4294967296)*(b0 w+b1 w*4294967296) := by
      simp only [UInt64.add_mul,UInt64.mul_add,upper_product_zero,UInt64.add_zero]
      ac_rfl
    _ = w.aLo*w.bLo := by rw [←ha,←hb]

end WNear.Proofs.SerializeMultiply
