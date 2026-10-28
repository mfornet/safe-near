import Binary.Code.Part21
import Bridge.Functions.U128From
import NearLogic.Tactic.Control
import Mathlib.Tactic.Ring

/-!
# `__multi3` (function 954), in the metered logic

`__multi3(out, al, ah, bl, bh)`, compiler_builtins' 128-bit multiplication
(wrapping): the `u128` `(al + 2^64 ah) * (bl + 2^64 bh) mod 2^128` written to
the 16 bytes at `out`, little-endian. The low word is the 32×32-bit
schoolbook product of `al` and `bl` with its two carries (`l10 < l7`,
`lo < l11`); the high word adds `bh * al + bl * ah`.

`f954_spec` is its `MFunSpec`: 60 instructions (activation, 12 locals, paid
by the caller). The arithmetic is `multi3_arith`.

Used by `core::fmt::num::fmt_u128` (902; its arithmetic in `FmtU128Div.lean`) to divide a `u128`
by `10^19`.
-/

namespace WNear.Binary.FmtMulti3

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.U128From (u128Bytes memBytes_split memBytes_join)

/-! ## The arithmetic -/



theorem u64_or_shift (c : UInt64) (w : UInt64) (hc : c.toNat ≤ 1) :
    (c <<< (32 % 64) ||| w >>> (32 % 64)).toNat = c.toNat * 2 ^ 32 + w.toNat / 2 ^ 32 := by
  have hw := w.toNat_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h
  · have : c = 0 := UInt64.toNat_inj.mp (by simpa using h)
    subst this
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  · have : c = 1 := UInt64.toNat_inj.mp (by simpa using h)
    subst this
    rw [UInt64.toNat_or]
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have : w.toNat / 4294967296 < 2 ^ 32 := by omega
    have key := Nat.two_pow_add_eq_or_of_lt this 1
    norm_num at key ⊢
    omega

theorem boolToU64 (b : Bool) : (Numeric.bool b).toUInt64.toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem multi3_arith (al ah bl bh : UInt64) :
    let l7 : UInt64 := (bl &&& (4294967295 : UInt64)) * al >>> ((32 : UInt64) % 64)
    let l10 := l7 + bl >>> (32 % 64) * (al &&& 4294967295)
    let l11 := l10 <<< (32 % 64)
    let lo := l11 + (bl &&& 4294967295) * (al &&& 4294967295)
    let hi := ((Numeric.bool (Numeric.irelop64 IRelOp.lt_u l10 l7)).toUInt64 <<< (32 % 64) |||
          l10 >>> (32 % 64)) + bl >>> (32 % 64) * al >>> (32 % 64) +
        (Numeric.bool (Numeric.irelop64 IRelOp.lt_u lo l11)).toUInt64 + (bh * al + bl * ah)
    lo.toNat + 2 ^ 64 * hi.toNat =
      (al.toNat + 2 ^ 64 * ah.toNat) * (bl.toNat + 2 ^ 64 * bh.toNat) % 2 ^ 128 := by
  intro l7 l10 l11 lo hi
  have ha := al.toNat_lt
  have hb := bl.toNat_lt
  have hA0 : (al &&& 4294967295).toNat = al.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have hB0 : (bl &&& 4294967295).toNat = bl.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have hA1 : (al >>> (32 % 64)).toNat = al.toNat / 2 ^ 32 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have hB1 : (bl >>> (32 % 64)).toNat = bl.toNat / 2 ^ 32 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  generalize ea0 : al.toNat % 2 ^ 32 = a0 at hA0
  generalize ea1 : al.toNat / 2 ^ 32 = a1 at hA1
  generalize eb0 : bl.toNat % 2 ^ 32 = b0 at hB0
  generalize eb1 : bl.toNat / 2 ^ 32 = b1 at hB1
  have hal : al.toNat = a1 * 2 ^ 32 + a0 := by omega
  have hbl : bl.toNat = b1 * 2 ^ 32 + b0 := by omega
  have ha0 : a0 < 2 ^ 32 := by omega
  have ha1 : a1 < 2 ^ 32 := by omega
  have hb0 : b0 < 2 ^ 32 := by omega
  have hb1 : b1 < 2 ^ 32 := by omega
  have p10 : b0 * a1 < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' hb0 ha1; simpa using this
  have p01 : b1 * a0 < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' hb1 ha0; simpa using this
  have p00 : b0 * a0 < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' hb0 ha0; simpa using this
  have p11 : b1 * a1 < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' hb1 ha1; simpa using this
  have h7 : l7.toNat = b0 * a1 := by
    simp only [l7, UInt64.toNat_mul, hB0, hA1]; exact Nat.mod_eq_of_lt p10
  have h10 : l10.toNat = (b0 * a1 + b1 * a0) % 2 ^ 64 := by
    simp only [l10, UInt64.toNat_add, h7, UInt64.toNat_mul, hB1, hA0, Nat.mod_eq_of_lt p01]
  have h11 : l11.toNat = l10.toNat % 2 ^ 32 * 2 ^ 32 := by
    simp only [l11, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := l10.toNat_lt
    simp
    omega
  have hlo : lo.toNat = (l11.toNat + b0 * a0) % 2 ^ 64 := by
    simp only [lo, UInt64.toNat_add, UInt64.toNat_mul, hB0, hA0, Nat.mod_eq_of_lt p00]
  have hc1 : (Numeric.bool (Numeric.irelop64 IRelOp.lt_u l10 l7)).toUInt64.toNat =
      (b0 * a1 + b1 * a0) / 2 ^ 64 := by
    rw [boolToU64]; simp only [Numeric.irelop64, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, h10, h7]
    split <;> omega
  have hc2 : (Numeric.bool (Numeric.irelop64 IRelOp.lt_u lo l11)).toUInt64.toNat =
      (l11.toNat + b0 * a0) / 2 ^ 64 := by
    have := l11.toNat_lt
    rw [boolToU64]; simp only [Numeric.irelop64, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hlo]
    split <;> omega
  have hor := u64_or_shift (Numeric.bool (Numeric.irelop64 IRelOp.lt_u l10 l7)).toUInt64 l10
    (by rw [hc1]; omega)
  have hhi : hi.toNat = ((b0 * a1 + b1 * a0) / 2 ^ 64 * 2 ^ 32 + l10.toNat / 2 ^ 32 + b1 * a1 +
      (l11.toNat + b0 * a0) / 2 ^ 64 + (bh.toNat * al.toNat + bl.toNat * ah.toNat)) % 2 ^ 64 := by
    simp only [hi, UInt64.toNat_add, UInt64.toNat_mul, hor, hc1, hc2, hB1, hA1, Nat.mod_eq_of_lt p11]
    omega
  rw [hlo, hhi, h11, h10]
  have e1 : (al.toNat + 2 ^ 64 * ah.toNat) * (bl.toNat + 2 ^ 64 * bh.toNat) =
      al.toNat * bl.toNat + 2 ^ 64 * (bh.toNat * al.toNat + bl.toNat * ah.toNat) +
        2 ^ 128 * (ah.toNat * bh.toNat) := by ring
  have e2 : al.toNat * bl.toNat = b1 * a1 * 2 ^ 64 + (b0 * a1 + b1 * a0) * 2 ^ 32 + b0 * a0 := by
    rw [hal, hbl]; ring
  rw [e1, e2]
  generalize bh.toNat * al.toNat + bl.toNat * ah.toNat = M
  generalize ah.toNat * bh.toNat = W
  generalize b0 * a1 + b1 * a0 = S at *
  generalize b1 * a1 = P11 at *
  generalize b0 * a0 = P00 at *
  omega

/-! ## The function -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of `__multi3(out, al, ah, bl, bh)`: the 16 bytes at `out`. -/
def pre (n : Nat) (out : UInt32) (al ah bl bh : UInt64) (ob : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i64 al, .i64 ah, .i64 bl, .i64 bh]⌝ ∗ n ↦[wms][ out.toNat ] ob)

/-- The postcondition: the product modulo `2^128` at `out`. -/
def post (n : Nat) (out : UInt32) (al ah bl bh : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ lo hi : UInt64, ⌜lo.toNat + 2 ^ 64 * hi.toNat =
      (al.toNat + 2 ^ 64 * ah.toNat) * (bl.toNat + 2 ^ 64 * bh.toNat) % 2 ^ 128⌝ ∗
    n ↦[wms][ out.toNat ] u128Bytes lo hi)

/-- `__multi3` (function 954 of `contract.wasm`): 60 instructions. -/
theorem f954_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out : UInt32) (al ah bl bh : UInt64)
    (ob : List UInt8) (hob : ob.length = 16) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f954 Cg (pre n out al ah bl bh ob)
      (fun _ => 60 * cfg.regularOpCost) (post n out al ah bl bh) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  icases memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho1, Ho2⟩
  simp only [f954]
  repeat mstep
  mstep [Ho1]
  repeat mstep
  mstep [Ho2]
  iunfold post
  iframe Hc
  isplitr
  · ipureintro; rfl
  iexists _, _
  isplitr
  · ipureintro; exact multi3_arith al ah bl bh
  rw [u128Bytes]
  iapply memBytes_join n out.toNat 8 _ _ (by simp) $$ [Ho1 Ho2]
  isplitl [Ho1] <;> iassumption

end Spec

end WNear.Binary.FmtMulti3
