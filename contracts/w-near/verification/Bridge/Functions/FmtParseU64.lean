import Binary.Code.Part19
import Bridge.Functions.FmtDigits
import NearLogic.Tactic.Control

/-!
# `core::fmt::num::imp::parse_u64_into` (function 900), in the metered logic

`parse_u64_into(v, buf, cp)`: the decimal digits of the `u64` `v` written
*backwards* before `buf + *cp`, two at a time from the lookup table `lut`
(1070974), `*cp` moved back over them. Straight-line code, no loop:

* `*cp ≤ 19` (signed) panics (excluded: `20 ≤ c`, the buffer holds any `u64`);
* path A, `v ≥ 10^16`: 16 digits (8 pairs, `pad16`), then the rest `v / 10^16`;
* path B, `10^8 ≤ v < 10^16`: 8 digits (4 pairs, `pad8`), then `v / 10^8`;
* path C, `v < 10^8`: the rest is `v`;
* the rest `q < 10^8` (`tail4`): 4 digits if `q ≥ 10^4` (`tail4`), 2 if the
  remainder is `≥ 100` (`tail2`), then 1 or 2 (`tail1`), each `return`ing.

`f900_spec`: for `20 ≤ c < 2^31`, `buf + c ≤ 2^32`, owning the
`(decDigits v).length` bytes before `buf + c`, the cursor word at `cp` and the
table, the bytes become `decDigits v` and the cursor `c - (decDigits v).length`.
Cost `cost v` `regular_op_cost`s (activation, 8 locals, paid by the caller):
`17 + cost4 v`, `103 + cost4 (v / 10^8)`, `175 + cost4 (v / 10^16)` on paths
C, B, A; `cost4 q ≤ 116`, so at most 245 (path A, `cost4 ≤ 70` there).

The tails are separate theorems taking the continuation `K` as a wand (and
stated on `bodyX.drop k`, reached from the stepped goal by `change`), so each
proof term stays small.

Pitfalls met:
* `c + 4294967292` (the cursor moved back) must be rewritten to
  `UInt32.ofNat (c.toNat - 4)` (`addNeg`) right after the `i32.add`, or the
  kernel runs out of stack;
* `simp only [Nat.add_zero, Nat.reduceMod, …]` on an address equation made the
  *kernel* check take ~55 s per address (156 s for the file); `fmt_addr`
  rewrites the `+ 0` with `rw` first, then the `toNat` lemmas (12 s for the file);
* `iapply` does not unfold `bodyX.drop k` to the literal code: `change` first.
-/

namespace WNear.Binary.FmtParseU64

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.FmtDigits

/-- The body of the outer block of `parse_u64_into` (900). -/
noncomputable def bodyX : List Instr := match f900.body with | .block _ b :: _ => b | _ => []

theorem addNeg (c m : UInt32) (k : Nat) (hm : m.toNat = 2 ^ 32 - k) (hk : k ≤ c.toNat) :
    c + m = UInt32.ofNat (c.toNat - k) := by
  apply UInt32.toNat_inj.mp
  have := c.toNat_lt
  rw [UInt32.toNat_add, hm, UInt32.toNat_ofNat']
  by_cases h0 : k = 0
  · subst h0; simp
  · rw [Nat.mod_eq_of_lt (a := c.toNat - k) (by omega)]; omega

theorem shl1 (y : UInt32) : (y <<< (1 % 32)).toNat = y.toNat * 2 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft]
  simp [Nat.shiftLeft_eq]

theorem shl1' (y : UInt32) : (y <<< 1).toNat = y.toNat * 2 % 2 ^ 32 := shl1 y


theorem u32_and_65535 (x : UInt32) : (x &&& 65535).toNat = x.toNat % 65536 := by
  rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 16

theorem u32_and_255 (x : UInt32) : (x &&& 255).toNat = x.toNat % 256 := by
  rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem storeBytes_digit (x : UInt32) (h : x.toNat < 10) :
    storeBytes (Value.i32 (x + 48)) 1 = [digit x.toNat] := by
  have e : (x + 48).toNat = 48 + x.toNat := by rw [UInt32.toNat_add]; simp; omega
  simp [storeBytes, storeRaw, digit, List.range, List.range.loop, e]

/-- Address and index equations: `toNat` of `UInt32` arithmetic, then `omega`. -/
macro "fmt_addr" : tactic => `(tactic|
  ((try rw [Nat.add_zero]); simp only [UInt32.toNat_add, UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_div, UInt32.toNat_mod, shl1, shl1', u32_and_65535, u32_and_255, UInt32.reduceToNat, UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod, UInt64.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv]; omega))

section Tail

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The frame of `parse_u64_into` at any point: `(v, buf, cp)` and its five locals. -/
def fr (inst : Nat) (mi : ModuleInst) (v : UInt64) (buf cp x3 : UInt32) (q4 q5 : UInt64) (x6 x7 : UInt32) :
    Frame := ⟨#[.i64 v, .i32 buf, .i32 cp, .i32 x3, .i64 q4, .i64 q5, .i32 x6, .i32 x7], inst, mi⟩

/-- What remains after the outer block: the panic. -/
def Ψ (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType) (Cg : Nat) (Φf : FunPost GF) :
    Post NearState GF :=
  Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d (f900.body.drop 1) (Post.mfunc cfg Cg type.results.length Φf))

/-- The continuation: the cursor moved back over the `L` bytes now holding `ds`. -/
def K (n : Nat) (buf cp c : UInt32) (L : Nat) (ds : List UInt8) (R : Nat) (Cg : Nat) (Φf : FunPost GF) :
    IProp GF :=
  iprop(∀ c' : UInt32, ⌜c'.toNat = c.toNat - L⌝ -∗ credits Cg R -∗ n ↦[i32][ cp.toNat ] c' -∗
    n ↦[wms][ buf.toNat + c.toNat - L ] ds -∗ n ↦[wms][ 1070974 ] lut -∗ Φf.ret [])

/-- The cost of the last one or two digits (`return` included). -/
def cost1 (x : Nat) : Nat := if x < 10 then 21 else 26

/-- The last one or two digits: `x3 < 100`. -/
theorem tail1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (Φf : FunPost GF) (v : UInt64) (buf cp c x3 : UInt32)
    (q4 q5 : UInt64) (x6 x7 : UInt32) (hx : x3.toNat < 100) (hc1 : 1 ≤ c.toNat)
    (hbc : buf.toNat + c.toNat ≤ 2 ^ 32) (hcL : (decDigits x3.toNat).length ≤ c.toNat) (ob : List UInt8) (hob : ob.length = (decDigits x3.toNat).length)
    (R : Nat) :
    credits Cg (cost1 x3.toNat * cfg.regularOpCost + R) ∗ n ↦[i32][ cp.toNat ] c ∗
      n ↦[wms][ buf.toNat + c.toNat - (decDigits x3.toNat).length ] ob ∗ n ↦[wms][ 1070974 ] lut ∗
      K n buf cp c (decDigits x3.toNat).length (decDigits x3.toNat) R Cg Φf
      ⊢ mwpi cfg lim d (fr inst mi v buf cp x3 q4 q5 x6 x7) [] (bodyX.drop 9) (Ψ cfg lim d type Cg Φf) := by
  iintro ⟨Hc, Hp, Hb, Hl, HK⟩
  simp only [bodyX, f900, List.drop, fr, Ψ]
  by_cases h10 : x3.toNat < 10
  · have e1 : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (x3 &&& 65535) 9) = 0 := by
      have h := u32_and_65535 x3
      simp only [Numeric.bool, Numeric.irelop32, gt_iff_lt, UInt32.lt_iff_toNat_lt, h]
      simp; omega
    have hL : decDigits x3.toNat = [digit x3.toNat] := decDigits_lt10 _ h10
    simp only [hL, List.length_singleton] at hob hcL ⊢
    clear hL
    simp only [cost1, h10, ite_true]
    obtain ⟨b, rfl⟩ : ∃ b, ob = [b] := List.length_eq_one_iff.mp hob
    repeat mstep
    mstep [Hp]
    repeat mstep
    mstep [Hp]; mstep; mstep
    rw [addNeg c 4294967295 1 rfl (by omega)]
    repeat mstep
    mstep [Hb]
    repeat mstep
    rw [storeBytes_digit x3 h10]
    iunfold K at HK
    iapply HK $$ %(UInt32.ofNat (c.toNat - 1)) %(by simp; omega) Hc Hp Hb Hl
  · have e1 : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (x3 &&& 65535) 9) = 1 := by
      have h := u32_and_65535 x3
      simp only [Numeric.bool, Numeric.irelop32, gt_iff_lt, UInt32.lt_iff_toNat_lt, h]
      simp; omega
    have hL : decDigits x3.toNat = padDigits 2 x3.toNat :=
      decDigits_eq_pad 1 _ (by simp; omega) (by simp; omega)
    simp only [hL, padDigits_length] at hob hcL ⊢
    clear hL
    simp only [cost1, h10, ite_false]
    icases lut_focus n x3.toNat hx $$ Hl with ⟨Hlp, Hlb⟩
    repeat mstep
    mstep [Hp]
    repeat mstep
    rw [addNeg c 4294967294 2 rfl (by omega)]
    mstep [Hp]
    repeat mstep
    mstep [Hlp] with (rw [UInt32.toNat_add, shl1, u32_and_65535]; simp; omega)
    mstep [Hb]
    rw [storeBytes_load16' _ (padDigits_length 2 _)]
    repeat mstep
    ihave Hl := Hlb $$ Hlp
    iunfold K at HK
    iapply HK $$ %(UInt32.ofNat (c.toNat - 2)) %(by simp; omega) Hc Hp Hb Hl

/-- The cost of the last two to four digits (`return` included). -/
def cost2 (x : Nat) : Nat := if x < 100 then 7 + cost1 x else 35 + cost1 (x / 100)

/-- The last two to four digits: `x3 < 10000`. -/
theorem tail2 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (Φf : FunPost GF) (v : UInt64) (buf cp c x3 : UInt32)
    (q4 q5 : UInt64) (x6 x7 : UInt32) (hx : x3.toNat < 10000) (hc1 : 1 ≤ c.toNat)
    (hbc : buf.toNat + c.toNat ≤ 2 ^ 32) (hcL : (decDigits x3.toNat).length ≤ c.toNat) (ob : List UInt8) (hob : ob.length = (decDigits x3.toNat).length)
    (R : Nat) :
    credits Cg (cost2 x3.toNat * cfg.regularOpCost + R) ∗ n ↦[i32][ cp.toNat ] c ∗
      n ↦[wms][ buf.toNat + c.toNat - (decDigits x3.toNat).length ] ob ∗ n ↦[wms][ 1070974 ] lut ∗
      K n buf cp c (decDigits x3.toNat).length (decDigits x3.toNat) R Cg Φf
      ⊢ mwpi cfg lim d (fr inst mi v buf cp x3 q4 q5 x6 x7) [] (bodyX.drop 8) (Ψ cfg lim d type Cg Φf) := by
  iintro ⟨Hc, Hp, Hb, Hl, HK⟩
  simp only [bodyX, f900, List.drop, fr, Ψ]
  by_cases h100 : x3.toNat < 100
  · have e1 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (x3 &&& 65535) 100) = 1 := by
      have h := u32_and_65535 x3
      simp only [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, h]
      simp; omega
    simp only [cost2, h100, ite_true, Nat.add_mul, Nat.add_assoc]
    iterate 8 mstep
    change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi v buf cp x3 q4 q5 (x3 &&& 65535) x7) [] (bodyX.drop 9) (Ψ cfg lim d type Cg Φf))
    iapply tail1 cfg lim d type htype inst mi n hn Cg Φf v buf cp c x3 q4 q5 (x3 &&& 65535) x7 h100 (by omega) hbc hcL ob hob R
    iframe Hc Hp Hb Hl HK
  · have e1 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (x3 &&& 65535) 100) = 0 := by
      have h := u32_and_65535 x3
      simp only [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, h]
      simp; omega
    simp only [cost2, h100, ite_false, Nat.add_mul, Nat.add_assoc]
    have hL := decDigits_length_split 2 x3.toNat (by simp; omega)
    simp only [Nat.reducePow] at hL
    generalize hL' : (decDigits (x3.toNat / 100)).length = L' at hL
    have hL1 : 1 ≤ L' := hL' ▸ decDigits_length_pos _
    icases memBytes_split2 n _ L' ob (by omega) $$ Hb with ⟨Hb1, Hb2⟩
    ihave Hb2 := memBytes_at n _ (b := buf.toNat + (c.toNat - 2)) (by omega) $$ Hb2
    icases lut_focus n (x3.toNat % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
    repeat mstep
    mstep [Hp]
    mstep; mstep
    rw [addNeg c 4294967294 2 rfl (by omega)]
    mstep; mstep [Hp]
    repeat mstep
    mstep [Hlp] with fmt_addr
    mstep [Hb2]
    rw [storeBytes_load16' _ (padDigits_length 2 _)]
    iterate 2 mstep
    have hq : ((x3 &&& 65535) / 100).toNat = x3.toNat / 100 := by fmt_addr
    change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi v buf cp ((x3 &&& 65535) / 100) q4 q5
      ((x3 &&& 65535) / 100) (UInt32.ofNat (c.toNat - 2))) [] (bodyX.drop 9) (Ψ cfg lim d type Cg Φf))
    iapply tail1 cfg lim d type htype inst mi n hn Cg Φf v buf cp (UInt32.ofNat (c.toNat - 2))
      ((x3 &&& 65535) / 100) q4 q5 ((x3 &&& 65535) / 100) (UInt32.ofNat (c.toNat - 2)) (by omega)
      (by simp; omega) (by simp; omega) (by rw [hq]; simp; omega) (ob.take L') (by rw [hq]; simp; omega) R
    rw [hq, hL']
    have hc2 : (UInt32.ofNat (c.toNat - 2)).toNat = c.toNat - 2 := by simp; omega
    ihave Hl := Hlb $$ Hlp
    iframe Hc Hp Hl
    isplitl [Hb1]
    · iapply memBytes_at n _ (by rw [hc2]; omega) $$ Hb1
    iunfold K
    iintro %c' %hc' Hc Hp Hd Hl
    iunfold K at HK
    iapply HK $$ %c' %(by rw [hc2] at hc'; omega) Hc Hp [Hd Hb2] Hl
    rw [hL, decDigits_split 2 x3.toNat (by simp; omega), ← padDigits_mod 2 x3.toNat]
    simp only [Nat.reducePow]
    iapply memBytes_join2 n _ L' _ _ hL' $$ [Hd Hb2]
    isplitl [Hd]
    · iapply memBytes_at n _ (by rw [hc2]; omega) $$ Hd
    · iapply memBytes_at n _ (by omega) $$ Hb2
/-- The cost of the last one to eight digits (`return` included). -/
def cost4 (x : Nat) : Nat := if x < 10000 then 9 + cost2 x else 55 + cost2 (x / 10000)

/-- The last one to eight digits: `q4 < 10^8`. -/
theorem tail4 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (Φf : FunPost GF) (v : UInt64) (buf cp c x3 : UInt32)
    (q4 q5 : UInt64) (x6 x7 : UInt32) (hq : q4.toNat < 100000000) (hc1 : 1 ≤ c.toNat)
    (hbc : buf.toNat + c.toNat ≤ 2 ^ 32) (hcL : (decDigits q4.toNat).length ≤ c.toNat) (ob : List UInt8)
    (hob : ob.length = (decDigits q4.toNat).length) (R : Nat) :
    credits Cg (cost4 q4.toNat * cfg.regularOpCost + R) ∗ n ↦[i32][ cp.toNat ] c ∗
      n ↦[wms][ buf.toNat + c.toNat - (decDigits q4.toNat).length ] ob ∗ n ↦[wms][ 1070974 ] lut ∗
      K n buf cp c (decDigits q4.toNat).length (decDigits q4.toNat) R Cg Φf
      ⊢ mwpi cfg lim d (fr inst mi v buf cp x3 q4 q5 x6 x7) [] (bodyX.drop 7) (Ψ cfg lim d type Cg Φf) := by
  iintro ⟨Hc, Hp, Hb, Hl, HK⟩
  simp only [bodyX, f900, List.drop, fr, Ψ]
  have hq32 : q4.toUInt32.toNat = q4.toNat := by simp; omega
  by_cases h4 : q4.toNat < 10000
  · have e1 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u q4.toUInt32 10000) = 0 := by
      simp only [Numeric.bool, Numeric.irelop32, ge_iff_le, UInt32.le_iff_toNat_le, hq32]
      simp; omega
    simp only [cost4, h4, ite_true, Nat.add_mul, Nat.add_assoc]
    iterate 11 mstep
    change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi v buf cp q4.toUInt32 q4 q5
      q4.toUInt32 x7) [] (bodyX.drop 8) (Ψ cfg lim d type Cg Φf))
    iapply tail2 cfg lim d type htype inst mi n hn Cg Φf v buf cp c q4.toUInt32 q4 q5 q4.toUInt32 x7
      (by omega) (by omega) hbc (by rw [hq32]; omega) ob (by rw [hq32]; omega) R
    rw [hq32]
    iframe Hc Hp Hb Hl HK
  · have e1 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u q4.toUInt32 10000) = 1 := by
      simp only [Numeric.bool, Numeric.irelop32, ge_iff_le, UInt32.le_iff_toNat_le, hq32]
      simp; omega
    simp only [cost4, h4, ite_false, Nat.add_mul, Nat.add_assoc]
    have hL := decDigits_length_split 4 q4.toNat (by simp; omega)
    simp only [Nat.reducePow] at hL
    generalize hL' : (decDigits (q4.toNat / 10000)).length = L' at hL
    have hL1 : 1 ≤ L' := hL' ▸ decDigits_length_pos _
    icases memBytes_split2 n _ L' ob (by omega) $$ Hb with ⟨Hb1, Hb2⟩
    icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨Hb2, Hb3⟩
    ihave Hb2 := memBytes_at n _ (b := buf.toNat + (c.toNat - 4)) (by omega) $$ Hb2
    ihave Hb3 := memBytes_at n _ (b := buf.toNat + (c.toNat - 4) + 2) (by omega) $$ Hb3
    icases lut_focus n (q4.toNat % 10000 / 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
    repeat mstep
    mstep [Hp]
    mstep; mstep
    rw [addNeg c 4294967292 4 rfl (by omega)]
    mstep; mstep [Hp]
    repeat mstep
    mstep [Hlp] with fmt_addr
    mstep [Hb2]
    rw [storeBytes_load16' _ (padDigits_length 2 _)]
    ihave Hl := Hlb $$ Hlp
    icases lut_focus n (q4.toNat % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
    repeat mstep
    mstep [Hp]
    repeat mstep
    mstep [Hlp] with fmt_addr
    mstep [Hb3]
    rw [storeBytes_load16' _ (padDigits_length 2 _)]
    ihave Hl := Hlb $$ Hlp
    have hq3 : (q4.toUInt32 / 10000).toNat = q4.toNat / 10000 := by rw [UInt32.toNat_div, hq32]; rfl
    have hc4 : (UInt32.ofNat (c.toNat - 4)).toNat = c.toNat - 4 := by simp; omega
    change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi v buf cp (q4.toUInt32 / 10000) q4 q5
      (q4.toUInt32 - q4.toUInt32 / 10000 * 10000)
      ((q4.toUInt32 - q4.toUInt32 / 10000 * 10000 &&& 65535) / 100)) [] (bodyX.drop 8) (Ψ cfg lim d type Cg Φf))
    iapply tail2 cfg lim d type htype inst mi n hn Cg Φf v buf cp (UInt32.ofNat (c.toNat - 4))
      (q4.toUInt32 / 10000) q4 q5 (q4.toUInt32 - q4.toUInt32 / 10000 * 10000)
      ((q4.toUInt32 - q4.toUInt32 / 10000 * 10000 &&& 65535) / 100) (by rw [hq3]; omega)
      (by rw [hc4]; omega) (by rw [hc4]; omega) (by rw [hq3, hc4]; omega) (ob.take L')
      (by rw [hq3]; simp; omega) R
    rw [hq3, hL']
    iframe Hc Hp Hl
    isplitl [Hb1]
    · iapply memBytes_at n _ (by rw [hc4]; omega) $$ Hb1
    iunfold K
    iintro %c' %hc' Hc Hp Hd Hl
    iunfold K at HK
    iapply HK $$ %c' %(by rw [hc4] at hc'; omega) Hc Hp [Hd Hb2 Hb3] Hl
    rw [hL, decDigits_split 4 q4.toNat (by simp; omega), padDigits_add 2 2,
      ← padDigits_mod 2 (q4.toNat / 10 ^ 2), ← padDigits_mod 2 q4.toNat]
    simp only [Nat.reducePow]
    rw [show q4.toNat / 100 % 100 = q4.toNat % 10000 / 100 by omega, ← List.append_assoc]
    iapply memBytes_join2 n _ (L' + 2) _ _ (by simp [hL']) $$ [Hd Hb2 Hb3]
    isplitl [Hd Hb2]
    · iapply memBytes_join2 n _ L' _ _ hL' $$ [Hd Hb2]
      isplitl [Hd]
      · iapply memBytes_at n _ (by rw [hc4]; omega) $$ Hd
      · iapply memBytes_at n _ (by omega) $$ Hb2
    · iapply memBytes_at n _ (by omega) $$ Hb3

end Tail

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The precondition of `parse_u64_into(v, buf, cp)`: the cursor `c` at `cp`, the
`(decDigits v).length` bytes before `buf + c`, the table. -/
def pre (n : Nat) (v : UInt64) (buf cp c : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i64 v, .i32 buf, .i32 cp]⌝ ∗ n ↦[i32][ cp.toNat ] c ∗
    n ↦[wms][ buf.toNat + c.toNat - (decDigits v.toNat).length ] ob ∗ n ↦[wms][ 1070974 ] lut)

/-- The postcondition: the digits written before `buf + c`, the cursor moved back over them. -/
def post (n : Nat) (v : UInt64) (buf cp c : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ c' : UInt32, ⌜c'.toNat = c.toNat - (decDigits v.toNat).length⌝ ∗
    n ↦[i32][ cp.toNat ] c' ∗ n ↦[wms][ buf.toNat + c.toNat - (decDigits v.toNat).length ] decDigits v.toNat ∗
    n ↦[wms][ 1070974 ] lut)

/-- The cost of `parse_u64_into`, activation excluded. -/
def cost (v : Nat) : Nat :=
  if v < 100000000 then 17 + cost4 v
  else if v < 10000000000000000 then 103 + cost4 (v / 100000000)
  else 175 + cost4 (v / 10000000000000000)

set_option maxHeartbeats 4000000 in
/-- **`parse_u64_into`** (function 900 of `contract.wasm`): the digits of `v` before `buf + c`. -/
theorem f900_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (v : UInt64) (buf cp c : UInt32)
    (hc1 : 20 ≤ c.toNat) (hc2 : c.toNat < 2 ^ 31) (hbc : buf.toNat + c.toNat ≤ 2 ^ 32)
    (ob : List UInt8) (hob : ob.length = (decDigits v.toNat).length) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f900 Cg (pre n v buf cp c ob)
      (fun _ => cost v.toNat * cfg.regularOpCost) (post n v buf cp c) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hp, Hb, Hl⟩
  subst hargs
  have hLv : (decDigits v.toNat).length ≤ 20 :=
    decDigits_length_le 20 _ (by omega) (by have := v.toNat_lt; omega)
  have hcs : Numeric.bool (Numeric.irelop32 IRelOp.le_s c 19) = 0 := by
    simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
  simp only [f900]
  by_cases hC : v.toNat < 100000000
  · have hA : Numeric.bool (Numeric.irelop64 IRelOp.lt_u v 10000000000000000) = 1 := by
      simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt]; omega
    have hB : Numeric.bool (Numeric.irelop64 IRelOp.ge_u v 100000000) = 0 := by
      simp [Numeric.bool, Numeric.irelop64, UInt64.le_iff_toNat_le]; omega
    simp only [cost, hC, ite_true, Nat.add_mul, Nat.add_assoc]
    mstep; mstep; mstep [Hp]
    iterate 19 mstep
    change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi v buf cp c v 0 0 0) [] (bodyX.drop 7)
      (Ψ cfg lim d type Cg _))
    iapply tail4 cfg lim d type htype inst mi n hn Cg _ v buf cp c c v 0 0 0 hC (by omega) hbc
      (by omega) ob hob R
    iframe Hc Hp Hb Hl
    iunfold K
    iintro %c' %hc' Hc Hp Hb Hl
    dsimp only
    iframe Hc
    iunfold post
    isplitr
    · ipureintro; rfl
    iexists c'
    iframe Hp Hb Hl
    ipureintro; exact hc'
  · by_cases hBB : v.toNat < 10000000000000000
    · have hA : Numeric.bool (Numeric.irelop64 IRelOp.lt_u v 10000000000000000) = 1 := by
        simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt]; omega
      have hB : Numeric.bool (Numeric.irelop64 IRelOp.ge_u v 100000000) = 1 := by
        simp [Numeric.bool, Numeric.irelop64, UInt64.le_iff_toNat_le]; omega
      simp only [cost, hC, hBB, ite_true, ite_false, Nat.add_mul, Nat.add_assoc]
      have hL := decDigits_length_split 8 v.toNat (by simp; omega)
      simp only [Nat.reducePow] at hL
      generalize hL' : (decDigits (v.toNat / 100000000)).length = L' at hL
      have hL1 : 1 ≤ L' := hL' ▸ decDigits_length_pos _
      icases memBytes_split2 n _ L' ob (by omega) $$ Hb with ⟨Hb1, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P0, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P1, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P2, P3⟩
      ihave P0 := memBytes_at n _ (b := buf.toNat + (c.toNat - 8)) (by omega) $$ P0
      ihave P1 := memBytes_at n _ (b := buf.toNat + (c.toNat - 8) + 2) (by omega) $$ P1
      ihave P2 := memBytes_at n _ (b := buf.toNat + (c.toNat - 8) + 4) (by omega) $$ P2
      ihave P3 := memBytes_at n _ (b := buf.toNat + (c.toNat - 8) + 6) (by omega) $$ P3
      mstep; mstep; mstep [Hp]
      iterate 20 mstep
      rw [addNeg c 4294967288 8 rfl (by omega)]
      mstep; mstep [Hp]
      icases lut_focus n (v.toNat % 10 ^ 8 / 10 ^ 6 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P0]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 8 / 10 ^ 4 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P1]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 8 / 10 ^ 2 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P2]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 8 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P3]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      have hq : (v / 100000000).toNat = v.toNat / 100000000 := by rw [UInt64.toNat_div]; rfl
      have hc8 : (UInt32.ofNat (c.toNat - 8)).toNat = c.toNat - 8 := by simp; omega
      change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi v buf cp
        ((v - v / 100000000 * 100000000).toUInt32 - (v - v / 100000000 * 100000000).toUInt32 / 100 * 100)
        (v / 100000000) 0 6 0) [] (bodyX.drop 7) (Ψ cfg lim d type Cg _))
      iapply tail4 cfg lim d type htype inst mi n hn Cg _ v buf cp (UInt32.ofNat (c.toNat - 8)) _
        (v / 100000000) 0 6 0 (by rw [hq]; omega) (by rw [hc8]; omega) (by rw [hc8]; omega)
        (by rw [hq, hc8]; omega) (ob.take L') (by rw [hq]; simp; omega) R
      rw [hq, hL']
      iframe Hc Hp Hl
      isplitl [Hb1]
      · iapply memBytes_at n _ (by rw [hc8]; omega) $$ Hb1
      iunfold K
      iintro %c' %hc' Hc Hp Hd Hl
      dsimp only
      iframe Hc
      iunfold post
      isplitr
      · ipureintro; rfl
      iexists c'
      iframe Hp Hl
      isplitr
      · ipureintro; rw [hc8] at hc'; omega
      rw [hL, decDigits_split 8 v.toNat (by simp; omega), pad8]
      simp only [Nat.reducePow, ← List.append_assoc]
      iapply memBytes_join2 n _ (L' + 6) _ _ (by simp [hL']) $$ [Hd P0 P1 P2 P3]
      isplitl [Hd P0 P1 P2]
      · iapply memBytes_join2 n _ (L' + 4) _ _ (by simp [hL']) $$ [Hd P0 P1 P2]
        isplitl [Hd P0 P1]
        · iapply memBytes_join2 n _ (L' + 2) _ _ (by simp [hL']) $$ [Hd P0 P1]
          isplitl [Hd P0]
          · iapply memBytes_join2 n _ L' _ _ hL' $$ [Hd P0]
            isplitl [Hd]
            · iapply memBytes_at n _ (by rw [hc8]; omega) $$ Hd
            · iapply memBytes_at n _ (by omega) $$ P0
          · iapply memBytes_at n _ (by omega) $$ P1
        · iapply memBytes_at n _ (by omega) $$ P2
      · iapply memBytes_at n _ (by omega) $$ P3
    · have hA : Numeric.bool (Numeric.irelop64 IRelOp.lt_u v 10000000000000000) = 0 := by
        simp [Numeric.bool, Numeric.irelop64, UInt64.lt_iff_toNat_lt]; omega
      simp only [cost, hC, hBB, ite_false, Nat.add_mul, Nat.add_assoc]
      have hL := decDigits_length_split 16 v.toNat (by simp; omega)
      simp only [Nat.reducePow] at hL
      generalize hL' : (decDigits (v.toNat / 10000000000000000)).length = L' at hL
      have hL1 : 1 ≤ L' := hL' ▸ decDigits_length_pos _
      icases memBytes_split2 n _ L' ob (by omega) $$ Hb with ⟨Hb1, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P0, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P1, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P2, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P3, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P4, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P5, Hb2⟩
      icases memBytes_split2 n _ 2 _ (by simp; omega) $$ Hb2 with ⟨P6, Hb2⟩
      ihave P0 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 0) (by omega) $$ P0
      ihave P1 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 2) (by omega) $$ P1
      ihave P2 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 4) (by omega) $$ P2
      ihave P3 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 6) (by omega) $$ P3
      ihave P4 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 8) (by omega) $$ P4
      ihave P5 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 10) (by omega) $$ P5
      ihave P6 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 12) (by omega) $$ P6
      ihave P7 := memBytes_at n _ (b := buf.toNat + (c.toNat - 16) + 14) (by omega) $$ Hb2
      mstep; mstep; mstep [Hp]
      iterate 15 mstep
      rw [addNeg c 4294967280 16 rfl (by omega)]
      mstep; mstep [Hp]
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 14 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P0]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 12 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P1]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 10 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P2]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 8 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P3]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 6 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P4]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 4 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P5]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 / 10 ^ 2 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P6]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      icases lut_focus n (v.toNat % 10 ^ 16 % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      mstep [Hp]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [P7]
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      ihave Hl := Hlb $$ Hlp
      have hq : (v / 10000000000000000).toNat = v.toNat / 10000000000000000 := by
        rw [UInt64.toNat_div]; rfl
      have hc8 : (UInt32.ofNat (c.toNat - 16)).toNat = c.toNat - 16 := by simp; omega
      change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi _ buf cp _
        (v / 10000000000000000) _ _ _) [] (bodyX.drop 7) (Ψ cfg lim d type Cg _))
      iapply tail4 cfg lim d type htype inst mi n hn Cg _ _ buf cp (UInt32.ofNat (c.toNat - 16)) _
        (v / 10000000000000000) _ _ _ (by rw [hq]; have := v.toNat_lt; omega) (by rw [hc8]; omega)
        (by rw [hc8]; omega) (by rw [hq, hc8]; omega) (ob.take L') (by rw [hq]; simp; omega) R
      rw [hq, hL']
      iframe Hc Hp Hl
      isplitl [Hb1]
      · iapply memBytes_at n _ (by rw [hc8]; omega) $$ Hb1
      iunfold K
      iintro %c' %hc' Hc Hp Hd Hl
      dsimp only
      iframe Hc
      iunfold post
      isplitr
      · ipureintro; rfl
      iexists c'
      iframe Hp Hl
      isplitr
      · ipureintro; rw [hc8] at hc'; omega
      rw [hL, decDigits_split 16 v.toNat (by simp; omega), pad16]
      simp only [Nat.reducePow, ← List.append_assoc]
      iapply memBytes_join2 n _ (L' + 14) _ _ (by simp [hL']) $$ [Hd P0 P1 P2 P3 P4 P5 P6 P7]
      isplitr [P7]
      swap
      · iapply memBytes_at n _ (by omega) $$ P7
      iapply memBytes_join2 n _ (L' + 12) _ _ (by simp [hL']) $$ [Hd P0 P1 P2 P3 P4 P5 P6]
      isplitr [P6]
      swap
      · iapply memBytes_at n _ (by omega) $$ P6
      iapply memBytes_join2 n _ (L' + 10) _ _ (by simp [hL']) $$ [Hd P0 P1 P2 P3 P4 P5]
      isplitr [P5]
      swap
      · iapply memBytes_at n _ (by omega) $$ P5
      iapply memBytes_join2 n _ (L' + 8) _ _ (by simp [hL']) $$ [Hd P0 P1 P2 P3 P4]
      isplitr [P4]
      swap
      · iapply memBytes_at n _ (by omega) $$ P4
      iapply memBytes_join2 n _ (L' + 6) _ _ (by simp [hL']) $$ [Hd P0 P1 P2 P3]
      isplitr [P3]
      swap
      · iapply memBytes_at n _ (by omega) $$ P3
      iapply memBytes_join2 n _ (L' + 4) _ _ (by simp [hL']) $$ [Hd P0 P1 P2]
      isplitr [P2]
      swap
      · iapply memBytes_at n _ (by omega) $$ P2
      iapply memBytes_join2 n _ (L' + 2) _ _ (by simp [hL']) $$ [Hd P0 P1]
      isplitr [P1]
      swap
      · iapply memBytes_at n _ (by omega) $$ P1
      iapply memBytes_join2 n _ L' _ _ hL' $$ [Hd P0]
      isplitl [Hd]
      · iapply memBytes_at n _ (by rw [hc8]; omega) $$ Hd
      · iapply memBytes_at n _ (by omega) $$ P0

end Spec
end WNear.Binary.FmtParseU64
