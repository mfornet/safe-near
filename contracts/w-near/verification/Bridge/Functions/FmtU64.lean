import Bridge.Functions.FmtU128
import Bridge.Functions.FmtWriteN
import Binary.Code.Part18
import Binary.Code.Part20

/-!
# `core::fmt::num::imp::fmt_u64` (936) below `10^4`, and `<u32 as Display>::fmt` (870)

```wat
;; 870 <u32 as Display>::fmt(x, f)     fmt_u64(*x as u64, true, f) (936)
;; 936 fmt_u64(v, is_nonneg, f)        sp -= 48; cur := 39
;;   v ≥ 10^4 ⇒ the loop: four digits at a time from the table (not taken here)
;;   v > 99 ⇒ cur -= 2; buf[cur..] := lut[v % 100]; v := v / 100
;;   v > 9  ⇒ cur -= 2; buf[cur..] := lut[v]   else cur -= 1; buf[cur] := '0' + v
;;   pad_integral(f, is_nonneg, "", 0, buf + cur, 39 - cur) (903); sp += 48
```

`buf` is `sp + 9`, so the digits end at `sp + 48`. `f936_small` covers `v < 10^4` (one to four
digits, no loop): the location's line and column. `pad_integral` (903, `FmtPad.f903_spec`) writes
the digits `decDigits v` with the sink's `write_str` (`sinkSpec64`: any specification for the
`decDigits v` bytes at `sp + 48 - |decDigits v|`, at the stack pointer `sp`).
-/

namespace WNear.Binary.FmtU64

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtDigits
open WNear.Binary.FmtPad (fmtr f903_spec)
open WNear.Binary.FmtWriteN (fmtrP)
open WNear.Binary.FmtParseU64 (shl1 shl1' u32_and_65535 storeBytes_digit)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro)
open WNear.Binary.AllocNewCell (memBytes_addr)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The sink's `write_str` on the digits `ds`, at the stack pointer `sp`: they end at `sp + 48`. -/
def sinkSpec64 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (sp data : UInt32) (code : Func) (ds : List UInt8) (Sk Sk' : IProp GF) (Kw Cg : Nat) :
    IProp GF :=
  iprop(□ (∀ p : UInt32, ∀ k : UInt32, ⌜p.toNat = sp.toNat + 48 - ds.length ∧ k.toNat = ds.length⌝ -∗
    MFunSpec cfg lim d types[15]! inst mi code Cg
      (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        n ↦[wms][ p.toNat ] ds ∗ Sk)) (fun _ => Kw)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ p.toNat ] ds ∗ Sk'))))

instance (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (sp data : UInt32) (code : Func) (ds : List UInt8) (Sk Sk' : IProp GF) (Kw Cg : Nat) :
    Persistent (sinkSpec64 cfg lim d inst mi n g gt sp data code ds Sk Sk' Kw Cg) := by
  unfold sinkSpec64; infer_instance

/-- 936's cost below `10^4`, the activation excluded. -/
noncomputable def cost936 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  200 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw

theorem act3 (c : Nat) (code : Func) (a b e : UInt32) :
    activationGas c (entryLocals code [.i32 a, .i32 b, .i32 e]) =
      activationGas c (entryLocals code [.i32 0, .i32 0, .i32 0]) := by
  simp [activationGas, entryLocals]

/-- `stk_split` at a size given as a sum. -/
theorem stk_split' (n a k k1 k2 : Nat) (h : k = k1 + k2) :
    stk (GF := GF) n a k ⊢ stk n a k1 ∗ stk n (a + k1) k2 := by
  subst h; exact stk_split n a k1 k2

theorem toU32_lt (v : UInt64) (h : v.toNat < 10000) : (v.toUInt32).toNat = v.toNat := by
  simp [UInt64.toNat_toUInt32]; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- 936's end: `pad_integral` (903) on the digits `ds` at `sp + 9 + c`, then `sp += 48`. -/
theorem tail936 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (Φf : FunPost GF)
    (gt : GlobalType) (s f data vtab idx c : UInt32) (v x5 : UInt64) (x6 x7 x8 : UInt32)
    (hs : 48 ≤ s.toNat) (hc : c.toNat ≤ 39) (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32)
    (a : Nat) (code : Func) (ds : List UInt8) (hds : ds.length = 39 - c.toNat) (Sk Sk' : IProp GF)
    (Kw R : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec64 cfg lim (d + 2) inst mi n g gt (s - 48) data code ds Sk Sk' Kw Cg ∗
      credits Cg (90 * cfg.regularOpCost + activationGas cfg.regularOpCost
        (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw + R) ∗
      g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ n ↦[wms][ (s - 48 + 9 + c).toNat ] ds ∗ fmtr n ta f data vtab idx a ∗ Sk ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 s⟩ -∗ n ↦[wms][ (s - 48 + 9 + c).toNat ] ds -∗
        fmtr n ta f data vtab idx a -∗ Sk' -∗ Φf.ret [.i32 0])
      ⊢ mwpi cfg lim d ⟨#[.i64 v, .i32 1, .i32 f, .i32 (s - 48), .i32 c, .i64 x5, .i32 x6, .i32 x7, .i32 x8],
          inst, mi⟩
          [.i32 f, .i32 1, .i32 1067136, .i32 0, .i32 (s - 48 + 9 + c), .i32 (39 - c)]
          [.call 903, .local_set 4, .local_get 3, .i32_const 48, .i32_binop .add, .global_set 0, .local_get 4]
          (Post.mfunc cfg Cg type.results.length Φf) := by
  iintro ⟨#H903, #H910, #Hi, #Ha, #Sw, Hc, Hg, Hds, HF, HS, HK⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha903 := hm.funcs 903 (by decide)
  have t67 : types[67]!.params.length = 6 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hp : (s - 48 + 9 + c).toNat = (s - 48).toNat + 48 - ds.length := by
    simp [UInt32.toNat_add, h48]; omega
  have hk : (39 - c).toNat = ds.length := by
    rw [UInt32.toNat_sub_of_le]; · simp; omega
    simp [UInt32.le_iff_toNat_le]; omega
  iunfold sinkSpec64 at Sw
  ihave #S := Sw $$ %(s - 48 + 9 + c) %(39 - c) %⟨hp, hk⟩
  have S903 := f903_spec (GF := GF) cfg lim (d + 1) types[67]! (by rfl) inst mi A n g ta hm (by omega) Cg f data
    vtab idx 1067136 0 (s - 48 + 9 + c) (39 - c) hf hvt a code
    iprop(g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ n ↦[wms][ (s - 48 + 9 + c).toNat ] ds ∗ Sk)
    iprop(g ↦[wg] ⟨gt, .i32 (s - 48)⟩ ∗ n ↦[wms][ (s - 48 + 9 + c).toNat ] ds ∗ Sk') Kw
  rw [act3 cfg.regularOpCost code data (s - 48 + 9 + c) (39 - c)] at S903
  generalize activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT at S903 ⊢
  mcall S903 using [HF Hg Hds HS]
  · iframe HF Hg Hds HS
  icases HQ with ⟨%hrs, HF, Hg, Hds, HS⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  repeat mstep
  rw [htype, Nat.sub_self, List.drop_zero]
  rw [show s - 48 + 48 = s by simp]
  mcredits R
  iapply HK $$ Hc Hg Hds HF HS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`fmt_u64(v, true, f)`** (936) for `v < 10^4`: the digits `decDigits v` in the frame, then
`pad_integral` (903) writes them with the sink's `write_str` (`sinkSpec64`). -/
theorem f936_small (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s f data vtab idx : UInt32) (v : UInt64) (hv : v.toNat < 10000) (hs : 48 ≤ s.toNat)
    (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func)
    (Sk Sk' : IProp GF) (Kw : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec64 cfg lim (d + 2) inst mi n g gt (s - 48) data code (decDigits v.toNat) Sk Sk' Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f936 Cg
        (fun args => iprop(⌜args = [.i64 v, .i32 1, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ fmtr n ta f data vtab idx a ∗ n ↦[wms][ 1070974 ] lut ∗ Sk))
        (fun _ => cost936 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ fmtr n ta f data vtab idx a ∗ n ↦[wms][ 1070974 ] lut ∗ Sk')) := by
  iintro ⟨#H903, #H910, #Hi, #Ha, #Sw⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha903 := hm.funcs 903 (by decide)
  have t67 : types[67]!.params.length = 6 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hL4 : (decDigits v.toNat).length ≤ 4 := decDigits_length_le 4 _ (by omega) (by simpa using hv)
  have hL1 := decDigits_length_pos v.toNat
  generalize hL : (decDigits v.toNat).length = L at hL4 hL1
  simp only [cost936]
  generalize hACT : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HF, Hl, HS⟩
  subst hargs
  ihave Hs := stk_addr (show s.toNat - 48 = (s - 48).toNat by omega) $$ Hs
  icases stk_split' n (s - 48).toNat 48 (48 - L) L (by omega) $$ Hs with ⟨Hlo, Hd⟩
  iunfold stk at Hd
  icases Hd with ⟨%ob, %hob, Hd⟩
  have hge : Numeric.bool (Numeric.irelop64 IRelOp.ge_u v 10000) = 0 := by
    simp [Numeric.irelop64, Numeric.bool, UInt64.le_iff_toNat_le]; omega
  have hx := toU32_lt v hv
  simp only [f936]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  by_cases h100 : v.toNat < 100
  · have hle : Numeric.bool (Numeric.irelop32 IRelOp.le_s v.toUInt32 99) = 1 := by
      simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
    by_cases h10 : v.toNat < 10
    · have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_s v.toUInt32 9) = 0 := by
        simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
      have hD : decDigits v.toNat = [digit v.toNat] := decDigits_lt10 _ h10
      have hL1' : L = 1 := by rw [← hL, hD]; simp
      subst hL1'
      rw [hD]
      repeat mstep
      rw [show (39 : UInt32) + 4294967295 = 38 from rfl]
      repeat mstep
      mstep [Hd] with (simp [UInt32.toNat_add, h48]; omega)
      rw [storeBytes_digit _ (by omega), hx]
      repeat mstep
      ihave Hd := memBytes_at n _ (b := (s - 48 + 9 + 38).toNat) (by simp [UInt32.toNat_add, h48]; omega) $$ Hd
      iapply tail936 cfg lim d type htype inst mi A n g ta hm hd Cg _ gt s f data vtab idx 38 v v v.toUInt32 0 0
        hs (by decide) hf hvt a code [digit v.toNat] (by simp) Sk Sk' Kw R
      rw [hACT]
      iframe H903 H910 Hi Ha Sw Hg Hd HF HS
      isplitl [Hc]
      · iapply credits_le; iframe Hc; ipureintro; omega
      iintro Hc Hg Hd HF HS
      dsimp only
      iframe Hc Hg HF Hl HS
      isplitr
      · ipureintro; rfl
      ihave Hd := FmtU128.stk_of n _ 1 _ (by simp) $$ Hd
      iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
      iapply stk_join n (s - 48).toNat 47 1
      iframe Hlo
      iapply stk_addr _ $$ Hd
      simp [UInt32.toNat_add, h48]; omega
    · have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_s v.toUInt32 9) = 1 := by
        simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
      have hD : decDigits v.toNat = padDigits 2 v.toNat :=
        decDigits_eq_pad 1 _ (by simp; omega) (by simp; omega)
      have hL2 : L = 2 := by rw [← hL, hD]; simp
      subst hL2
      rw [hD]
      icases lut_focus n v.toNat (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      rw [show (39 : UInt32) + 4294967294 = 37 from rfl]
      mstep [Hlp] with (rw [UInt32.toNat_add, shl1, hx]; simp; omega)
      mstep [Hd] with (simp [UInt32.toNat_add, h48]; omega)
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      repeat mstep
      ihave Hl := Hlb $$ Hlp
      ihave Hd := memBytes_at n _ (b := (s - 48 + 9 + 37).toNat) (by simp [UInt32.toNat_add, h48]; omega) $$ Hd
      iapply tail936 cfg lim d type htype inst mi A n g ta hm hd Cg _ gt s f data vtab idx 37 v v v.toUInt32 0 0
        hs (by decide) hf hvt a code (padDigits 2 v.toNat) (by simp) Sk Sk' Kw R
      rw [hACT]
      iframe H903 H910 Hi Ha Sw Hg Hd HF HS
      isplitl [Hc]
      · iapply credits_le; iframe Hc; ipureintro; omega
      iintro Hc Hg Hd HF HS
      dsimp only
      iframe Hc Hg HF Hl HS
      isplitr
      · ipureintro; rfl
      ihave Hd := FmtU128.stk_of n _ 2 _ (by simp) $$ Hd
      iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
      iapply stk_join n (s - 48).toNat 46 2
      iframe Hlo
      iapply stk_addr _ $$ Hd
      simp [UInt32.toNat_add, h48]; omega
  · have hle : Numeric.bool (Numeric.irelop32 IRelOp.le_s v.toUInt32 99) = 0 := by
      simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
    have hq : ((v.toUInt32 &&& 65535) / 100).toNat = v.toNat / 100 := by
      rw [UInt32.toNat_div, u32_and_65535, hx]; simp; omega
    have hDs := decDigits_split 2 v.toNat (by simp; omega)
    rw [← padDigits_mod 2 v.toNat] at hDs
    simp only [Nat.reducePow] at hDs
    have hL3 : L = (decDigits (v.toNat / 100)).length + 2 := by rw [← hL, hDs]; simp
    icases lut_focus n (v.toNat % 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
    icases memBytes_split2 n _ (L - 2) ob (by omega) $$ Hd with ⟨Hd1, Hd2⟩
    repeat mstep
    rw [show (39 : UInt32) + 4294967294 = 37 from rfl]
    mstep [Hlp] with fmt_addr
    mstep [Hd2] with (simp [UInt32.toNat_add, h48]; omega)
    rw [storeBytes_load16' _ (padDigits_length 2 _)]
    ihave Hl := Hlb $$ Hlp
    by_cases h1000 : v.toNat < 1000
    · have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_s ((v.toUInt32 &&& 65535) / 100) 9) = 0 := by
        simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
      have hD1 : decDigits (v.toNat / 100) = [digit (v.toNat / 100)] := decDigits_lt10 _ (by omega)
      rw [hD1] at hDs hL3
      simp only [List.length_singleton] at hL3
      simp only [List.singleton_append] at hDs
      subst hL3
      rw [hDs]
      repeat mstep
      rw [show (37 : UInt32) + 4294967295 = 36 from rfl]
      repeat mstep
      mstep [Hd1] with (simp [UInt32.toNat_add, h48]; omega)
      rw [storeBytes_digit _ (by omega), hq]
      repeat mstep
      ihave Hd := memBytes_join2 n _ 1 [digit (v.toNat / 100)] (padDigits 2 (v.toNat % 100)) (by simp) $$ [Hd1 Hd2]
      · isplitl [Hd1]
        · iexact Hd1
        iapply memBytes_at n _ (by omega) $$ Hd2
      ihave Hd := memBytes_at n _ (b := (s - 48 + 9 + 36).toNat) (by simp [UInt32.toNat_add, h48]; omega) $$ Hd
      simp only [List.singleton_append]
      iapply tail936 cfg lim d type htype inst mi A n g ta hm hd Cg _ gt s f data vtab idx 36 v v
        ((v.toUInt32 &&& 65535) / 100) 0 0 hs (by decide) hf hvt a code
        (digit (v.toNat / 100) :: padDigits 2 (v.toNat % 100)) (by simp) Sk Sk' Kw R
      rw [hACT]
      iframe H903 H910 Hi Ha Sw Hg Hd HF HS
      isplitl [Hc]
      · iapply credits_le; iframe Hc; ipureintro; omega
      iintro Hc Hg Hd HF HS
      dsimp only
      iframe Hc Hg HF Hl HS
      isplitr
      · ipureintro; rfl
      ihave Hd := FmtU128.stk_of n _ 3 _ (by simp) $$ Hd
      iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
      iapply stk_join n (s - 48).toNat 45 3
      iframe Hlo
      iapply stk_addr _ $$ Hd
      simp [UInt32.toNat_add, h48]; omega
    · have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_s ((v.toUInt32 &&& 65535) / 100) 9) = 1 := by
        simp only [Numeric.bool, Numeric.irelop32, UInt32.toIntS]; split <;> simp_all <;> omega
      have hD1 : decDigits (v.toNat / 100) = padDigits 2 (v.toNat / 100) :=
        decDigits_eq_pad 1 _ (by simp; omega) (by simp; omega)
      rw [hD1] at hDs hL3
      simp only [padDigits_length] at hL3
      subst hL3
      rw [hDs]
      icases lut_focus n (v.toNat / 100) (by omega) $$ Hl with ⟨Hlp, Hlb⟩
      repeat mstep
      rw [show (37 : UInt32) + 4294967294 = 35 from rfl]
      repeat mstep
      mstep [Hlp] with fmt_addr
      mstep [Hd1] with (simp [UInt32.toNat_add, h48]; omega)
      rw [storeBytes_load16' _ (padDigits_length 2 _)]
      repeat mstep
      ihave Hl := Hlb $$ Hlp
      ihave Hd := memBytes_join2 n _ 2 (padDigits 2 (v.toNat / 100)) (padDigits 2 (v.toNat % 100)) (by simp)
        $$ [Hd1 Hd2]
      · isplitl [Hd1]
        · iexact Hd1
        iapply memBytes_at n _ (by omega) $$ Hd2
      ihave Hd := memBytes_at n _ (b := (s - 48 + 9 + 35).toNat) (by simp [UInt32.toNat_add, h48]; omega) $$ Hd
      iapply tail936 cfg lim d type htype inst mi A n g ta hm hd Cg _ gt s f data vtab idx 35 v v
        ((v.toUInt32 &&& 65535) / 100) 0 0 hs (by decide) hf hvt a code
        (padDigits 2 (v.toNat / 100) ++ padDigits 2 (v.toNat % 100)) (by simp) Sk Sk' Kw R
      rw [hACT]
      iframe H903 H910 Hi Ha Sw Hg Hd HF HS
      isplitl [Hc]
      · iapply credits_le; iframe Hc; ipureintro; omega
      iintro Hc Hg Hd HF HS
      dsimp only
      iframe Hc Hg HF Hl HS
      isplitr
      · ipureintro; rfl
      ihave Hd := FmtU128.stk_of n _ 4 _ (by simp) $$ Hd
      iapply stk_addr (show (s - 48).toNat = s.toNat - 48 by omega)
      iapply stk_join n (s - 48).toNat 44 4
      iframe Hlo
      iapply stk_addr _ $$ Hd
      simp [UInt32.toNat_add, h48]; omega

/-- 870's cost below `10^4`, the activation excluded. -/
noncomputable def cost870 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f936 [.i64 0, .i32 0, .i32 0]) +
    cost936 cfg code Kw

theorem load32u (w : UInt32) :
    loadValue .i64 (some { bits := 32, signed := false }) w.toNat = .i64 w.toUInt64 := by
  have hw := w.toNat_lt
  simp [loadValue]
  try (apply UInt64.toNat_inj.mp; simp; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<u32 as Display>::fmt(x, f)`** (870) on `*x = w < 10^4`: `fmt_u64(w, true, f)` (936). -/
theorem f870_small (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s x f data vtab idx w : UInt32) (hw : w.toNat < 10000) (hs : 48 ≤ s.toNat)
    (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func)
    (Sk Sk' : IProp GF) (Kw : Nat) :
    A 936 ↪[wf] FuncInst.wasm types[68]! inst f936 ∗
      A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec64 cfg lim (d + 3) inst mi n g gt (s - 48) data code (decDigits w.toNat) Sk Sk' Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f870 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ x.toNat ] w ∗ fmtr n ta f data vtab idx a ∗
          n ↦[wms][ 1070974 ] lut ∗ Sk))
        (fun _ => cost870 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ x.toNat ] w ∗ fmtr n ta f data vtab idx a ∗
          n ↦[wms][ 1070974 ] lut ∗ Sk')) := by
  iintro ⟨#H936, #H903, #H910, #Hi, #Ha, #Sw⟩
  have hn := hm.mem
  have ha936 := hm.funcs 936 (by decide)
  have t68 : types[68]!.params.length = 3 := by rfl
  have hwv : w.toUInt64.toNat < 10000 := by simp; omega
  have hww : w.toUInt64.toNat = w.toNat := by simp
  ihave #S936 := f936_small cfg lim (d + 1) types[68]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s f data
    vtab idx w.toUInt64 hwv hs hf hvt a code Sk Sk' Kw $$ [H903 H910 Hi Ha Sw]
  · rw [hww]; iframe H903 H910 Hi Ha Sw
  simp only [cost870]
  generalize hK : cost936 cfg code Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hx, HF, Hl, HS⟩
  subst hargs
  simp only [f870]
  repeat mstep
  mstep [Hx]
  rw [load32u]
  repeat mstep
  mcall S936 using [Hg Hs HF Hl HS]
  · iframe Hg Hs HF Hl HS
  icases HQ with ⟨%hrs, Hg, Hs, HF, Hl, HS⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc Hg Hs Hx HF Hl HS
  ipureintro; rw [htype]; rfl

end Spec

end WNear.Binary.FmtU64
