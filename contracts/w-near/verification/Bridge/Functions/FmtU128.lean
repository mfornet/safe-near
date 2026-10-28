import Bridge.Functions.FmtPad
import Bridge.Functions.FmtParseU64
import Bridge.Functions.FmtMulti3
import Bridge.Functions.FmtU128Div
import Bridge.Functions.MemSet

/-!
# `core::fmt::num::fmt_u128` (902), in the metered logic

See FmtDigits.lean for the design and FmtU128Div.lean for the arithmetic. The body, at the
top level (`f902.body`):

```
0–7    sp -= 144; *(sp + 140) = 39                               (the cursor)
8      block: the first division, fast (`hi ≤ 524287`) or slow (four `__multi3`)
9–27   rem = lo + low64(q · (2^128 - 10^19)) (954 at sp + 16); parse_u64_into(rem, sp + 101, sp + 140)
28     block: q ≠ 0 ⇒ zeros, the next 19 digits (954 at sp, 900), q2 ≠ 0 ⇒ zeros, one digit
29–48  pad_integral(f, true, "", 0, sp + 101 + c, 39 - c) (903); sp += 144
```

Each segment is a theorem on `f902.body.drop k` taking the rest as a wand.
-/

namespace WNear.Binary.FmtU128

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtDigits WNear.Binary.FmtU128Div
open WNear.Binary.FmtPad (fmtr f903_spec)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro)
open WNear.Binary.AllocNewCell (memBytes_addr)

theorem load_storeBytes_i64 (v : UInt64) :
    loadValue .i64 none (Memory.decodeLE (storeBytes (.i64 v) 8)) = .i64 v := by
  have hv := v.toNat_lt
  have e : Memory.decodeLE (storeBytes (.i64 v) 8) = v.toNat := by
    simp [storeBytes, storeRaw, Memory.decodeLE, List.range, List.range.loop, Nat.shiftRight_eq_div_pow]
    omega
  simp [loadValue, e]

theorem ofNat_decode_i64 (v : UInt64) : UInt64.ofNat (Memory.decodeLE (storeBytes (.i64 v) 8)) = v := by
  have hv := v.toNat_lt
  have e : Memory.decodeLE (storeBytes (.i64 v) 8) = v.toNat := by
    simp [storeBytes, storeRaw, Memory.decodeLE, List.range, List.range.loop, Nat.shiftRight_eq_div_pow]
    omega
  rw [e]; simp

/-- The frame of `fmt_u128`: `(lo, hi, is_nonnegative, f)` and its four locals. -/
def fr (inst : Nat) (mi : ModuleInst) (x0 x1 : UInt64) (x2 x3 x4 : UInt32) (x5 x6 : UInt64) (x7 : UInt32) :
    Frame := ⟨#[.i64 x0, .i64 x1, .i32 x2, .i32 x3, .i32 x4, .i64 x5, .i64 x6, .i32 x7], inst, mi⟩

/-- The activation of the sink's `write_str` on three `i32`s. -/
theorem act3 (c : Nat) (code : Func) (a b e : UInt32) :
    activationGas c (entryLocals code [.i32 a, .i32 b, .i32 e]) =
      activationGas c (entryLocals code [.i32 0, .i32 0, .i32 0]) := by
  simp [activationGas, entryLocals]

section Tail

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The sink's `write_str` on the `39 - c` bytes `ds` at `sp + 101 + c`. -/
def sinkSpec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (sp c data : UInt32) (code : Func) (ds : List UInt8) (Sk Sk' : IProp GF) (Kw Cg : Nat) :
    IProp GF :=
  iprop(□ (∀ p : UInt32, ∀ k : UInt32, ⌜p.toNat = sp.toNat + 101 + c.toNat ∧ k.toNat = 39 - c.toNat⌝ -∗
    MFunSpec cfg lim d types[15]! inst mi code Cg
      (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        n ↦[wms][ p.toNat ] ds ∗ Sk)) (fun _ => Kw)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ p.toNat ] ds ∗ Sk'))))

instance (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (sp c data : UInt32) (code : Func) (ds : List UInt8) (Sk Sk' : IProp GF) (Kw Cg : Nat) :
    Persistent (sinkSpec cfg lim d inst mi n g gt sp c data code ds Sk Sk' Kw Cg) := by
  unfold sinkSpec; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The end (29–48): `pad_integral` on the digits `ds` at `sp + 101 + c`, then `sp += 144`. -/
theorem tEnd (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (Φf : FunPost GF)
    (gt : GlobalType) (x0 x1 x5 x6 : UInt64) (x7 : UInt32) (sp f c data vtab idx : UInt32)
    (hsp : sp.toNat + 144 ≤ 2 ^ 32) (hc : c.toNat ≤ 39) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func) (ds : List UInt8) (Sk Sk' : IProp GF)
    (Kw R : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec cfg lim (d + 2) inst mi n g gt sp c data code ds Sk Sk' Kw Cg ∗
      credits Cg (101 * cfg.regularOpCost + activationGas cfg.regularOpCost
        (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ sp.toNat + 140 ] c ∗ n ↦[wms][ sp.toNat + 101 + c.toNat ] ds ∗
      fmtr n ta f data vtab idx a ∗ Sk ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ n ↦[i32][ sp.toNat + 140 ] c -∗
        n ↦[wms][ sp.toNat + 101 + c.toNat ] ds -∗ fmtr n ta f data vtab idx a -∗ Sk' -∗ Φf.ret [.i32 0])
      ⊢ mwpi cfg lim d (fr inst mi x0 x1 1 f sp x5 x6 x7) [] (f902.body.drop 29)
          (Post.mfunc cfg Cg type.results.length Φf) := by
  iintro ⟨#H903, #H910, #Hi, #Ha, #Sw, Hc, Hg, Hcur, Hds, HF, HS, HK⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha903 := hm.funcs 903 (by decide)
  have t67 : types[67]!.params.length = 6 := by rfl
  have hp : (sp + 101 + c).toNat = sp.toNat + 101 + c.toNat := by
    simp [UInt32.toNat_add]; omega
  have hk : (39 - c).toNat = 39 - c.toNat := by
    rw [UInt32.toNat_sub_of_le]; · rfl
    simp [UInt32.le_iff_toNat_le]; omega
  iunfold sinkSpec at Sw
  ihave #S := Sw $$ %(sp + 101 + c) %(39 - c) %⟨hp, hk⟩
  have S903 := f903_spec (GF := GF) cfg lim (d + 1) types[67]! (by rfl) inst mi A n g ta hm (by omega) Cg f data
    vtab idx 1067136 0 (sp + 101 + c) (39 - c) hf hvt a code
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ (sp + 101 + c).toNat ] ds ∗ Sk)
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[wms][ (sp + 101 + c).toNat ] ds ∗ Sk') Kw
  rw [act3 cfg.regularOpCost code data (sp + 101 + c) (39 - c)] at S903
  generalize activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT at S903 ⊢
  ihave Hds := memBytes_addr (show sp.toNat + 101 + c.toNat = (sp + 101 + c).toNat by omega) $$ Hds
  simp only [f902, fr, List.drop]
  repeat mstep
  mstep [Hcur]
  repeat mstep
  mcall S903 using [HF Hg Hds HS]
  · iframe HF Hg Hds HS
  icases HQ with ⟨%hrs, HF, Hg, Hds, HS⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  repeat mstep
  rw [htype, Nat.sub_self, List.drop_zero]
  mcredits R
  iapply HK $$ Hc Hg Hcur [Hds] HF HS
  iapply memBytes_addr (show (sp + 101 + c).toNat = sp.toNat + 101 + c.toNat by omega) $$ Hds


/-- The body of the rounds block (28). -/
noncomputable def rounds : List Instr := match f902.body.drop 28 with | .block _ b :: _ => b | _ => []

theorem store_digit (x : UInt64) (h : x.toNat < 10) :
    storeBytes (.i32 (x.toUInt32 ||| 48)) 1 = [digit x.toNat] := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 10 ∧ x = UInt64.ofNat k := ⟨x.toNat, h, by simp⟩
  interval_cases k <;> decide

theorem byteOf_48 : MemSet.byteOf 48 = digit 0 := rfl

/-- The cost of the third round (`rounds.drop 51`), the end excluded. -/
def costR3 (c2 : Nat) : Nat := 37 + MemSet.cost (c2 - 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The third round: `'0'`s at `[1, c2)`, the digit `q2` at 0, the cursor 0; then the end. -/
theorem tR3 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (Φf : FunPost GF)
    (gt : GlobalType) (x0 x1 x5 x6 : UInt64) (x7 : UInt32) (sp f c2 data vtab idx : UInt32)
    (hsp : sp.toNat + 144 ≤ 2 ^ 32) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hq2 : x0.toNat < 10) (hc2 : 1 ≤ c2.toNat ∧ c2.toNat ≤ 20)
    (a : Nat) (code : Func) (ob tl ds : List UInt8) (hob : ob.length = c2.toNat)
    (hds : ds = digit x0.toNat :: (List.replicate (c2.toNat - 1) (digit 0) ++ tl)) (Sk Sk' : IProp GF)
    (Kw R : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec cfg lim (d + 2) inst mi n g gt sp 0 data code ds Sk Sk' Kw Cg ∗
      credits Cg (costR3 c2.toNat * cfg.regularOpCost + (101 * cfg.regularOpCost + activationGas
        cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw + R)) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ sp.toNat + 140 ] c2 ∗ n ↦[wms][ sp.toNat + 101 ] ob ∗
      n ↦[wms][ sp.toNat + 101 + c2.toNat ] tl ∗ fmtr n ta f data vtab idx a ∗ Sk ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ n ↦[i32][ sp.toNat + 140 ] 0 -∗
        n ↦[wms][ sp.toNat + 101 + (0 : UInt32).toNat ] ds -∗ fmtr n ta f data vtab idx a -∗ Sk' -∗
        Φf.ret [.i32 0])
      ⊢ mwpi cfg lim d (fr inst mi x0 x1 1 f sp x5 x6 x7) [] (rounds.drop 51)
          (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d (f902.body.drop 29)
            (Post.mfunc cfg Cg type.results.length Φf))) := by
  iintro ⟨#H903, #H910, #H952, #Hi, #Ha, #Sw, Hc, Hg, Hcur, Hob, Htl, HF, HS, HK⟩
  have hn := hm.mem
  have ha952 := hm.funcs 952 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have hc1 : (UInt32.ofNat (c2.toNat - 1)).toNat = c2.toNat - 1 := by simp; omega
  icases U128From.memBytes_split n (sp.toNat + 101) 1 ob (by omega) $$ Hob with ⟨Hb0, Hb1⟩
  ihave Hb1 := memBytes_addr (show sp.toNat + 101 + 1 = (sp + 102).toNat by
    simp [UInt32.toNat_add]; omega) $$ Hb1
  generalize hM : MemSet.cost (c2.toNat - 1) = M
  have S952 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f952 Cg
      (MemSet.pre n (sp + 102) 48 (UInt32.ofNat (c2.toNat - 1)) (ob.drop 1))
      (fun _ => M * cfg.regularOpCost) (MemSet.post n (sp + 102) 48 (UInt32.ofNat (c2.toNat - 1))) := by
    have h := MemSet.f952_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (sp + 102) 48
      (UInt32.ofNat (c2.toNat - 1)) (ob.drop 1) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
    rw [hc1, hM] at h
    exact h
  generalize hACT : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  unfold costR3
  rw [hM, Nat.add_mul, Nat.add_assoc]
  generalize M * cfg.regularOpCost = MC at S952 ⊢
  simp only [rounds, f902, List.drop, fr]
  repeat mstep
  mstep [Hcur]
  repeat mstep
  rw [FmtParseU64.addNeg c2 4294967295 1 rfl (by omega)]
  mcall S952 using [Hb1]
  · iunfold MemSet.pre
    iframe Hb1
    ipureintro; rfl
  iunfold MemSet.post at HQ
  icases HQ with ⟨%hrs, Hz⟩
  subst hrs
  repeat mstep
  mstep [Hb0]
  repeat mstep
  mstep [Hcur]
  rw [store_digit x0 hq2, hc1, byteOf_48]
  ihave Hz := memBytes_addr (show (sp + 102).toNat = sp.toNat + 101 + 1 by simp [UInt32.toNat_add]; omega) $$ Hz
  ihave Htl := memBytes_addr (show sp.toNat + 101 + c2.toNat = sp.toNat + 101 + 1 + (c2.toNat - 1) by omega) $$ Htl
  ihave Hzt := U128From.memBytes_join n (sp.toNat + 101 + 1) (c2.toNat - 1) (List.replicate (c2.toNat - 1) (digit 0)) tl (List.length_replicate ..) $$ [Hz Htl]
  · iframe Hz Htl
  ihave Hd := U128From.memBytes_join n (sp.toNat + 101) 1 [digit x0.toNat] _ rfl $$ [Hb0 Hzt]
  · iframe Hb0 Hzt
  rw [List.singleton_append, ← hds]
  change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi x0 x1 1 f sp x5 x6 x7) [] (f902.body.drop 29)
    (Post.mfunc cfg Cg type.results.length Φf))
  rw [← hACT]
  iapply tEnd cfg lim d type htype inst mi A n g ta hm hd Cg Φf gt x0 x1 x5 x6 x7 sp f 0 data vtab idx hsp
    (by simp) hf hvt a code ds Sk Sk' Kw R
  iframe H903 H910 Hi Ha Sw Hg Hcur HF HS
  isplitl [Hc]
  · iapply credits_le
    iframe Hc
    ipureintro; omega
  isplitl [Hd]
  · iapply memBytes_addr (show sp.toNat + 101 = sp.toNat + 101 + (0 : UInt32).toNat by simp) $$ Hd
  iintro Hc Hg Hcur Hd HF HS
  iapply HK $$ Hc Hg Hcur [Hd] HF HS
  iapply memBytes_addr (show sp.toNat + 101 + (0 : UInt32).toNat = sp.toNat + 101 by simp) $$ Hd


theorem buf43 (n sp c : Nat) (ob ds : List UInt8) (w : UInt32) (h1 : ob.length = c)
    (h2 : ds.length = 39 - c) (hc : c ≤ 39) :
    n ↦[wms][ sp + 101 ] ob ∗ n ↦[wms][ sp + 101 + c ] ds ∗ n ↦[i32][ sp + 140 ] w ⊢
      stk (GF := GF) n (sp + 101) 43 := by
  iintro ⟨H1, H2, H3⟩
  ihave H := U128From.memBytes_join n (sp + 101) c ob ds h1 $$ [H1 H2]
  · iframe H1 H2
  ihave H3 := memBytes_addr (show sp + 140 = sp + 101 + (ob ++ ds).length by simp; omega) $$ H3
  ihave H := U128From.memBytes_join n (sp + 101) _ (ob ++ ds) (bytes32 w) rfl $$ [H H3]
  · iframe H H3
  ihave H := stk_intro n _ _ $$ H
  rw [show (ob ++ ds ++ bytes32 w).length = 43 by simp; omega] at *
  iexact H

theorem join3 (n a i j : Nat) (A B C : List UInt8) (hA : A.length = i) (hB : B.length = j) :
    n ↦[wms][ a ] A ∗ n ↦[wms][ a + i ] B ∗ n ↦[wms][ a + i + j ] C ⊢
      memBytes (H := NearState) (GF := GF) n a (A ++ B ++ C) := by
  iintro ⟨H1, H2, H3⟩
  ihave H := U128From.memBytes_join n a i A B hA $$ [H1 H2]
  · iframe H1 H2
  iapply U128From.memBytes_join n a (i + j) (A ++ B) C (by simp; omega)
  iframe H
  rw [Nat.add_assoc] at *
  iexact H3

theorem lt_bool1 (y : UInt64) (h : y.toNat < 19073486328125) :
    Numeric.bool (Numeric.irelop64 IRelOp.lt_u y 19073486328125) = 1 := by
  simp [Numeric.irelop64, Numeric.bool, UInt64.lt_iff_toNat_lt]; omega

theorem lt_bool0 (y : UInt64) (h : 19073486328125 ≤ y.toNat) :
    Numeric.bool (Numeric.irelop64 IRelOp.lt_u y 19073486328125) = 0 := by
  simp [Numeric.irelop64, Numeric.bool, UInt64.lt_iff_toNat_lt]; omega

theorem stk_of (n a k : Nat) (bs : List UInt8) (h : bs.length = k) :
    n ↦[wms][ a ] bs ⊢ stk (GF := GF) n a k := by
  iintro H; iunfold stk; iexists bs; iframe H; ipureintro; exact h

theorem sinkSpec_c {cfg : WasmConfig} {lim : ExecLimits} {d inst : Nat} {mi : ModuleInst} {n g : Nat}
    {gt : GlobalType} {sp c c' data : UInt32} {code : Func} {ds : List UInt8} {Sk Sk' : IProp GF}
    {Kw Cg : Nat} (h : c.toNat = c'.toNat) :
    sinkSpec cfg lim d inst mi n g gt sp c data code ds Sk Sk' Kw Cg ⊢
      sinkSpec cfg lim d inst mi n g gt sp c' data code ds Sk Sk' Kw Cg := by
  have : c = c' := UInt32.toNat_inj.mp h
  subst this; exact .rfl

/-- What the caller gets back at the end: the 39-byte buffer and the cursor, the 16 bytes at `sp`. -/
def KK (n g : Nat) (gt : GlobalType) (sp : UInt32) (ta : Nat) (f data vtab idx : UInt32) (a : Nat)
    (Sk' : IProp GF) (R Cg : Nat) (Φf : FunPost GF) : IProp GF :=
  iprop(credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ stk n (sp.toNat + 101) 43 -∗
    stk n sp.toNat 16 -∗ n ↦[wms][ 1070974 ] lut -∗ fmtr n ta f data vtab idx a -∗ Sk' -∗ Φf.ret [.i32 0])

/-- The cost of the rounds block (28) for `N`, the end excluded. -/
def costRounds (N : Nat) : Nat :=
  if N / 10 ^ 19 = 0 then 5
  else 155 + MemSet.cost (19 - (decDigits (N % 10 ^ 19)).length) +
    FmtParseU64.cost (N / 10 ^ 19 % 10 ^ 19) +
    (if N / 10 ^ 19 / 10 ^ 19 = 0 then 0
     else costR3 (20 - (decDigits (N / 10 ^ 19 % 10 ^ 19)).length))

theorem or_ne_zero (a b : UInt64) (h : a.toNat + 2 ^ 64 * b.toNat ≠ 0) : (a ||| b == 0) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have h2 := congrArg UInt64.toNat heq
  rw [UInt64.toNat_or, UInt64.toNat_zero, Nat.or_eq_zero_iff] at h2
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The rounds block (28), from the first remainder's digits at `[c1, 39)`. -/
theorem tRounds (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (Φf : FunPost GF)
    (gt : GlobalType) (N : Nat) (hN : N < 2 ^ 128) (x0 x1 x5 x6 : UInt64) (x7 : UInt32)
    (hq : x1.toNat + 2 ^ 64 * x5.toNat = N / 10 ^ 19) (sp f c1 data vtab idx : UInt32)
    (hc1 : c1.toNat = 39 - (decDigits (N % 10 ^ 19)).length)
    (hsp : sp.toNat + 144 ≤ 2 ^ 32) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func) (ob m16 : List UInt8)
    (hob : ob.length = c1.toNat) (hm16 : m16.length = 16) (Sk Sk' : IProp GF) (Kw R : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗
      A 900 ↪[wf] FuncInst.wasm types[56]! inst f900 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec cfg lim (d + 2) inst mi n g gt sp (UInt32.ofNat (39 - (decDigits N).length)) data code
        (decDigits N) Sk Sk' Kw Cg ∗
      credits Cg (costRounds N * cfg.regularOpCost + (101 * cfg.regularOpCost + activationGas
        cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw + R)) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ sp.toNat + 140 ] c1 ∗ n ↦[wms][ sp.toNat + 101 ] ob ∗
      n ↦[wms][ sp.toNat + 101 + c1.toNat ] decDigits (N % 10 ^ 19) ∗ n ↦[wms][ sp.toNat ] m16 ∗
      n ↦[wms][ 1070974 ] lut ∗ fmtr n ta f data vtab idx a ∗ Sk ∗
      KK n g gt sp ta f data vtab idx a Sk' R Cg Φf
      ⊢ mwpi cfg lim d (fr inst mi x0 x1 1 f sp x5 x6 x7) [] (f902.body.drop 28)
          (Post.mfunc cfg Cg type.results.length Φf) := by
  iintro ⟨#H903, #H910, #H952, #H954, #H900, #Hi, #Ha, #Sw, Hc, Hg, Hcur, Hob, Hr1, Hm, Hl, HF, HS, HK⟩
  have hn := hm.mem
  have ha952 := hm.funcs 952 (by decide)
  have ha954 := hm.funcs 954 (by decide)
  have ha900 := hm.funcs 900 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t8 : types[8]!.params.length = 5 := by rfl
  have t56 : types[56]!.params.length = 3 := by rfl
  have hL1 : (decDigits (N % 10 ^ 19)).length ≤ 19 :=
    decDigits_length_le 19 _ (by norm_num) (Nat.mod_lt _ (by norm_num))
  have hdig := u128_digits N hN
  generalize hACT : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  by_cases hq0 : N / 10 ^ 19 = 0
  · ------------------------------------------------------------------ q = 0
    have hx1 : x1 = 0 := UInt64.toNat_inj.mp (by simp; omega)
    have hx5 : x5 = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hx1 hx5
    simp only [hq0, ite_true] at hdig
    simp only [costRounds, hq0, ite_true]
    simp only [f902, fr, List.drop]
    iterate 6 mstep
    simp only [Nat.reducePow] at hdig hc1 hL1
    ihave #Sw1 := sinkSpec_c (c' := c1) (by simp [hdig]; omega) $$ Sw
    rw [hdig] at *
    change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi x0 0 1 f sp 0 x6 x7) [] (f902.body.drop 29)
      (Post.mfunc cfg Cg type.results.length Φf))
    rw [← hACT]
    iapply tEnd cfg lim d type htype inst mi A n g ta hm hd Cg Φf gt x0 0 0 x6 x7 sp f c1 data vtab idx hsp
      (by omega) hf hvt a code (decDigits (N % 10000000000000000000)) Sk Sk' Kw R
    iframe H903 H910 Hi Ha Sw1 Hc Hg Hcur Hr1 HF HS
    iintro Hc Hg Hcur Hr1 HF HS
    iunfold KK at HK
    iapply HK $$ Hc Hg [Hob Hr1 Hcur] [Hm] Hl HF HS
    · iapply buf43 n sp.toNat c1.toNat ob (decDigits (N % 10000000000000000000)) c1 hob (by omega) (by omega)
      iframe Hob Hr1 Hcur
    · iunfold stk; iexists m16; iframe Hm; ipureintro; exact hm16
  · ------------------------------------------------------------------ q ≠ 0
    simp only [Nat.reducePow] at hdig hc1 hL1 hq hq0 ⊢
    have hqpos : x1.toNat + 2 ^ 64 * x5.toNat ≠ 0 := by omega
    have hor : Numeric.bool (x1 ||| x5 == 0) = 0 := by rw [or_ne_zero x1 x5 hqpos]; rfl
    have hqlt : N / 10000000000000000000 < 2 ^ 65 := by omega
    have hx5 : x5.toNat ≤ 1 := by omega
    have hL2 : (decDigits (N / 10000000000000000000 % 10000000000000000000)).length ≤ 19 :=
      decDigits_length_le 19 _ (by norm_num) (Nat.mod_lt _ (by norm_num))
    simp only [costRounds, hq0, ite_false, Nat.reducePow]
    generalize hX : (if N / 10000000000000000000 / 10000000000000000000 = 0 then 0 else
      costR3 (20 - (decDigits (N / 10000000000000000000 % 10000000000000000000)).length)) = X
    -- the memset of the zeros [20, c1)
    have hc20 : (UInt32.ofNat (c1.toNat - 20)).toNat = c1.toNat - 20 := by simp; omega
    generalize hM : MemSet.cost (19 - (decDigits (N % 10000000000000000000)).length) = M
    have S952 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f952 Cg
        (MemSet.pre n (sp + 101 + 20) 48 (UInt32.ofNat (c1.toNat - 20)) (ob.drop 20))
        (fun _ => M * cfg.regularOpCost) (MemSet.post n (sp + 101 + 20) 48 (UInt32.ofNat (c1.toNat - 20))) := by
      have h := MemSet.f952_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (sp + 101 + 20) 48
        (UInt32.ofNat (c1.toNat - 20)) (ob.drop 20) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
      have e : MemSet.cost (c1.toNat - 20) = M := by
        rw [← hM, show c1.toNat - 20 = 19 - (decDigits (N % 10000000000000000000)).length by omega]
      rw [hc20, e] at h
      exact h
    generalize hC9 : FmtParseU64.cost (N / 10000000000000000000 % 10000000000000000000) = C9
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
    generalize M * cfg.regularOpCost = MC at S952 ⊢
    icases U128From.memBytes_split n (sp.toNat + 101) 20 ob (by omega) $$ Hob with ⟨Hj, Hz⟩
    ihave Hz := memBytes_addr (show sp.toNat + 101 + 20 = (sp + 101 + 20).toNat by
      simp [UInt32.toNat_add]; omega) $$ Hz
    simp only [f902, fr, List.drop]
    iterate 6 mstep
    repeat mstep
    mstep [Hcur]
    repeat mstep
    rw [FmtParseU64.addNeg c1 4294967276 20 rfl (by omega)]
    mcall S952 using [Hz]
    · iunfold MemSet.pre
      iframe Hz
      ipureintro; rfl
    iunfold MemSet.post at HQ
    icases HQ with ⟨%hrs, Hz⟩
    subst hrs
    repeat mstep
    mstep [Hcur]
    repeat mstep
    -- the second division and its remainder
    have hq2v : ((x1 >>> (19 % 64) ||| x5 <<< (45 % 64)) / 19073486328125).toNat =
        N / 10000000000000000000 / 10000000000000000000 := by
      have := udiv_fast x1 x5 (by omega); simp only [Nat.reducePow] at this; rw [hq] at this; exact this
    mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! (by rfl) inst mi n hn Cg sp
        ((x1 >>> (19 % 64) ||| x5 <<< (45 % 64)) / 19073486328125) x1 8446744073709551616
        18446744073709551615 m16 hm16) using [Hm]
    · iunfold FmtMulti3.pre
      iframe Hm
      ipureintro; rfl
    iunfold FmtMulti3.post at HQ
    icases HQ with ⟨%hrs, %r0, %r1, %hr, Hm⟩
    subst hrs
    have hx1lt := x1.toNat_lt
    have hrem : (r0 + x1).toNat = N / 10000000000000000000 % 10000000000000000000 :=
      rem_words r0 r1 _ x1 x1 (N / 10000000000000000000) hr (by simp only [Nat.reducePow]; omega)
        (by rw [hq2v]; simp only [Nat.reducePow]; omega)
    rw [U128From.u128Bytes]
    icases (memBytes_append (GF := GF) (H := NearState) n sp.toNat _ _).1 $$ Hm with ⟨Hm0, Hm8⟩
    repeat mstep
    mstep [Hm0]
    rw [ofNat_decode_i64]
    repeat mstep
    -- the digits of the second remainder
    generalize hL2d : (decDigits (N / 10000000000000000000 % 10000000000000000000)).length = L2 at hL2
    icases U128From.memBytes_split n (sp.toNat + 101) (20 - L2) (ob.take 20) (by simp; omega) $$ Hj with ⟨Hj1, Hj2⟩
    have S900 := FmtParseU64.f900_spec (GF := GF) cfg lim (d + 1) types[56]! (by rfl) inst mi n hn Cg (r0 + x1)
      (sp + 101) (sp + 140) 20 (by decide) (by decide) (by simp [UInt32.toNat_add]; omega)
      ((ob.take 20).drop (20 - L2)) (by rw [hrem, hL2d]; simp; omega)
    rw [hrem, hC9] at S900
    generalize C9 * cfg.regularOpCost = C9c at S900 ⊢
    mcall S900 using [Hcur Hj2 Hl]
    · iunfold FmtParseU64.pre
      rw [hrem, hL2d]
      iframe Hl
      isplitr
      · ipureintro; rfl
      isplitl [Hcur]
      · iapply memBytes_addr (show sp.toNat + 140 = (sp + 140).toNat by simp [UInt32.toNat_add]; omega) $$ Hcur
      iapply memBytes_addr (show sp.toNat + 101 + (20 - L2) = (sp + 101).toNat + (20 : UInt32).toNat - L2 by
        simp [UInt32.toNat_add]; omega) $$ Hj2
    iunfold FmtParseU64.post at HQ
    icases HQ with ⟨%hrs, %c2, %hc2, Hcur, Hd2, Hl⟩
    subst hrs
    rw [hrem, hL2d] at hc2 ⊢
    replace hc2 : c2.toNat = 20 - L2 := by rw [hc2]; rfl
    -- the pieces back at their addresses
    rw [hc20, byteOf_48, show c1.toNat - 20 = 19 - (decDigits (N % 10000000000000000000)).length by omega]
    ihave Hz := memBytes_addr (show (sp + 101 + 20).toNat = sp.toNat + 101 + (20 - L2) + L2 by
      simp [UInt32.toNat_add]; omega) $$ Hz
    ihave Hd2 := memBytes_addr (show (sp + 101).toNat + UInt32.toNat 20 - L2 = sp.toNat + 101 + (20 - L2) by
      simp [UInt32.toNat_add]; omega) $$ Hd2
    ihave Hr1 := memBytes_addr (show sp.toNat + 101 + c1.toNat = sp.toNat + 101 + (20 - L2) + L2 +
      (19 - (decDigits (N % 10000000000000000000)).length) by omega) $$ Hr1
    ihave Htl := join3 n (sp.toNat + 101 + (20 - L2)) L2 (19 - (decDigits (N % 10000000000000000000)).length)
      _ _ _ hL2d (List.length_replicate ..) $$ [Hd2 Hz Hr1]
    · iframe Hd2 Hz Hr1
    ihave Hcur := memBytes_addr (show (sp + 140).toNat = sp.toNat + 140 by simp [UInt32.toNat_add]; omega) $$ Hcur
    ihave Hm8 := memBytes_addr (show sp.toNat + (storeBytes (.i64 r0) 8).length = sp.toNat + 8 by
      simp [storeBytes]) $$ Hm8
    ihave Hm := U128From.memBytes_join n sp.toNat 8 (storeBytes (.i64 r0) 8) (storeBytes (.i64 r1) 8)
      (by simp [storeBytes]) $$ [Hm0 Hm8]
    · iframe Hm0 Hm8
    have hy : (x1 >>> (19 % 64) ||| x5 <<< (45 % 64)).toNat / 19073486328125 =
        N / 10000000000000000000 / 10000000000000000000 := by rw [← hq2v, UInt64.toNat_div]; rfl
    simp only [hq0, ite_false] at hdig
    by_cases hq2 : N / 10000000000000000000 / 10000000000000000000 = 0
    · ---------------------------------------------------------------- two rounds
      have hlt : Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x1 >>> (19 % 64) ||| x5 <<< (45 % 64))
          19073486328125) = 1 := lt_bool1 _ (by omega)
      simp only [hq2, ite_true] at hdig hX
      subst hX
      iterate 4 mstep
      have htl : (decDigits (N / 10000000000000000000 % 10000000000000000000) ++
          List.replicate (19 - (decDigits (N % 10000000000000000000)).length) (digit 0) ++
          decDigits (N % 10000000000000000000)).length = 39 - c2.toNat := by simp; omega
      ihave #Sw1 := sinkSpec_c (c' := c2) (by rw [hdig, htl]; simp; omega) $$ Sw
      rw [hdig]
      change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi _ x1 1 f sp _ x6 x7) [] (f902.body.drop 29)
        (Post.mfunc cfg Cg type.results.length Φf))
      rw [← hACT]
      iapply tEnd cfg lim d type htype inst mi A n g ta hm hd Cg Φf gt _ x1 _ x6 x7 sp f c2 data vtab idx hsp
        (by omega) hf hvt a code (decDigits (N / 10000000000000000000 % 10000000000000000000) ++
          List.replicate (19 - (decDigits (N % 10000000000000000000)).length) (digit 0) ++
          decDigits (N % 10000000000000000000)) Sk Sk' Kw R
      iframe H903 H910 Hi Ha Sw1 Hg Hcur HF HS
      isplitl [Hc]
      · iapply credits_le
        iframe Hc
        ipureintro; omega
      isplitl [Htl]
      · simp only [List.append_assoc]
        iapply memBytes_addr (show sp.toNat + 101 + (20 - L2) = sp.toNat + 101 + c2.toNat by omega) $$ Htl
      iintro Hc Hg Hcur Hd HF HS
      iunfold KK at HK
      iapply HK $$ Hc Hg [Hj1 Hd Hcur] [Hm] Hl HF HS
      · iapply buf43 n sp.toNat c2.toNat (List.take (20 - L2) (List.take 20 ob)) _ c2 (by simp; omega) htl (by omega)
        iframe Hj1 Hd Hcur
      · iunfold stk; iexists (storeBytes (.i64 r0) 8 ++ storeBytes (.i64 r1) 8); iframe Hm
        ipureintro; first | rfl | trivial | simp
    · ---------------------------------------------------------------- three rounds
      have hge : Numeric.bool (Numeric.irelop64 IRelOp.lt_u (x1 >>> (19 % 64) ||| x5 <<< (45 % 64))
          19073486328125) = 0 := lt_bool0 _ (by omega)
      simp only [hq2, ite_false] at hdig hX
      subst hX
      iterate 4 mstep
      have hq2lt : ((x1 >>> (19 % 64) ||| x5 <<< (45 % 64)) / 19073486328125).toNat < 10 := by
        rw [hq2v]; omega
      rw [hL2d] at hdig
      have hlen : (decDigits N).length = 39 := by rw [hdig]; simp; omega
      ihave #Sw1 := sinkSpec_c (c' := 0) (by rw [hlen]; rfl) $$ Sw
      have hds : decDigits N = digit ((x1 >>> (19 % 64) ||| x5 <<< (45 % 64)) / 19073486328125).toNat ::
          (List.replicate (c2.toNat - 1) (digit 0) ++
            (decDigits (N / 10000000000000000000 % 10000000000000000000) ++
              List.replicate (19 - (decDigits (N % 10000000000000000000)).length) (digit 0) ++
              decDigits (N % 10000000000000000000))) := by
        rw [hdig, hq2v, show c2.toNat - 1 = 19 - L2 by omega]; simp [List.append_assoc]
      rw [hL2d, show 20 - L2 = c2.toNat by omega]
      change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi _ x1 1 f sp _ x6 x7) [] (rounds.drop 51)
        (Post.mblock cfg Cg 0 [] (Post.mseq cfg lim d (f902.body.drop 29)
          (Post.mfunc cfg Cg type.results.length Φf))))
      rw [← hACT]
      iapply tR3 cfg lim d type htype inst mi A n g ta hm hd Cg Φf gt _ x1 _ x6 x7 sp f c2 data vtab idx hsp
        hf hvt hq2lt (by omega) a code (List.take c2.toNat (List.take 20 ob)) _ (decDigits N) (by simp; omega) hds
        Sk Sk' Kw R
      iframe H903 H910 H952 Hi Ha Sw1 Hg Hcur HF HS Hj1
      isplitl [Hc]
      · iapply credits_le
        iframe Hc
        ipureintro; omega
      isplitl [Htl]
      · simp only [List.append_assoc]
        iexact Htl
      iintro Hc Hg Hcur Hd HF HS
      iunfold KK at HK
      iapply HK $$ Hc Hg [Hd Hcur] [Hm] Hl HF HS
      · iapply buf43 n sp.toNat 0 [] (decDigits N) 0 rfl (by rw [hlen]) (by omega)
        iframe Hcur
        isplitr
        · iapply VecFromElem.memBytes_nil
        iapply memBytes_addr (show sp.toNat + 101 + UInt32.toNat 0 = sp.toNat + 101 + 0 by rfl) $$ Hd
      · iunfold stk; iexists (storeBytes (.i64 r0) 8 ++ storeBytes (.i64 r1) 8); iframe Hm
        ipureintro; first | rfl | trivial | simp


/-- The cost of the first remainder and its digits (9–27). -/
def costR1 (N : Nat) : Nat := 113 + FmtParseU64.cost (N % 10 ^ 19)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The first remainder (9–27): `N mod 10^19` from `lo` and `q = N / 10^19`, its digits before 39. -/
theorem tR1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (Φf : FunPost GF)
    (gt : GlobalType) (N : Nat) (hN : N < 2 ^ 128) (x0 x1 x5 x6 : UInt64) (x7 : UInt32)
    (hx0 : x0.toNat = N % 2 ^ 64) (hq : x1.toNat + 2 ^ 64 * x5.toNat = N / 10 ^ 19)
    (sp f data vtab idx : UInt32) (hsp : sp.toNat + 144 ≤ 2 ^ 32) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func) (ob m0 m1 : List UInt8)
    (hob : ob.length = 39) (hm0 : m0.length = 16) (hm1 : m1.length = 16) (Sk Sk' : IProp GF) (Kw R : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗
      A 900 ↪[wf] FuncInst.wasm types[56]! inst f900 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec cfg lim (d + 2) inst mi n g gt sp (UInt32.ofNat (39 - (decDigits N).length)) data code
        (decDigits N) Sk Sk' Kw Cg ∗
      credits Cg ((costR1 N + costRounds N) * cfg.regularOpCost + (101 * cfg.regularOpCost +
        activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw + R)) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ sp.toNat + 140 ] 39 ∗ n ↦[wms][ sp.toNat + 101 ] ob ∗
      n ↦[wms][ sp.toNat ] m0 ∗ n ↦[wms][ sp.toNat + 16 ] m1 ∗
      n ↦[wms][ 1070974 ] lut ∗ fmtr n ta f data vtab idx a ∗ Sk ∗
      (credits Cg R -∗ g ↦[wg] ⟨gt, .i32 (sp + 144)⟩ -∗ stk n (sp.toNat + 101) 43 -∗
        stk n sp.toNat 32 -∗ n ↦[wms][ 1070974 ] lut -∗ fmtr n ta f data vtab idx a -∗ Sk' -∗
        Φf.ret [.i32 0])
      ⊢ mwpi cfg lim d (fr inst mi x0 x1 1 f sp x5 x6 x7) [] (f902.body.drop 9)
          (Post.mfunc cfg Cg type.results.length Φf) := by
  iintro ⟨#H903, #H910, #H952, #H954, #H900, #Hi, #Ha, #Sw, Hc, Hg, Hcur, Hob, Hm0, Hm1, Hl, HF, HS, HK⟩
  have hn := hm.mem
  have ha954 := hm.funcs 954 (by decide)
  have ha900 := hm.funcs 900 (by decide)
  have t8 : types[8]!.params.length = 5 := by rfl
  have t56 : types[56]!.params.length = 3 := by rfl
  have hL1 : (decDigits (N % 10 ^ 19)).length ≤ 19 :=
    decDigits_length_le 19 _ (by norm_num) (Nat.mod_lt _ (by norm_num))
  have hx1lt := x1.toNat_lt
  generalize hACT : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  generalize hCR : costRounds N = CR
  generalize hC9 : FmtParseU64.cost (N % 10 ^ 19) = C9
  unfold costR1
  rw [hC9]
  simp only [Nat.add_mul]
  generalize hCRc : CR * cfg.regularOpCost = CRc
  generalize hC9c : C9 * cfg.regularOpCost = C9c
  ihave Hm1 := memBytes_addr (show sp.toNat + 16 = (sp + 16).toNat by simp [UInt32.toNat_add]; omega) $$ Hm1
  simp only [f902, fr, List.drop]
  repeat mstep
  mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! (by rfl) inst mi n hn Cg (sp + 16) x1 x5
      8446744073709551616 18446744073709551615 m1 hm1) using [Hm1]
  · iunfold FmtMulti3.pre
    iframe Hm1
    ipureintro; rfl
  iunfold FmtMulti3.post at HQ
  icases HQ with ⟨%hrs, %r0, %r1, %hr, Hm1⟩
  subst hrs
  have hrem : (r0 + x0).toNat = N % 10 ^ 19 :=
    rem_words r0 r1 x1 x5 x0 N hr hx0 (by omega)
  rw [U128From.u128Bytes]
  icases (memBytes_append (GF := GF) (H := NearState) n (sp + 16).toNat _ _).1 $$ Hm1 with ⟨Hm10, Hm18⟩
  ihave Hm10 := memBytes_addr (show (sp + 16).toNat = sp.toNat + 16 by simp [UInt32.toNat_add]; omega) $$ Hm10
  repeat mstep
  mstep [Hm10]
  rw [ofNat_decode_i64]
  repeat mstep
  -- the digits of the first remainder
  generalize hL1d : (decDigits (N % 10 ^ 19)).length = L1 at hL1
  icases U128From.memBytes_split n (sp.toNat + 101) (39 - L1) ob (by omega) $$ Hob with ⟨Hj1, Hj2⟩
  have S900 := FmtParseU64.f900_spec (GF := GF) cfg lim (d + 1) types[56]! (by rfl) inst mi n hn Cg (r0 + x0)
    (sp + 101) (sp + 140) 39 (by decide) (by decide) (by simp [UInt32.toNat_add]; omega)
    (ob.drop (39 - L1)) (by rw [hrem, hL1d]; simp; omega)
  rw [hrem, hC9, hC9c] at S900
  mcall S900 using [Hcur Hj2 Hl]
  · iunfold FmtParseU64.pre
    rw [hrem, hL1d]
    iframe Hl
    isplitr
    · ipureintro; rfl
    isplitl [Hcur]
    · iapply memBytes_addr (show sp.toNat + 140 = (sp + 140).toNat by simp [UInt32.toNat_add]; omega) $$ Hcur
    iapply memBytes_addr (show sp.toNat + 101 + (39 - L1) = (sp + 101).toNat + (39 : UInt32).toNat - L1 by
      simp [UInt32.toNat_add]; omega) $$ Hj2
  iunfold FmtParseU64.post at HQ
  icases HQ with ⟨%hrs, %c1, %hc1, Hcur, Hd1, Hl⟩
  subst hrs
  rw [hrem, hL1d] at hc1 ⊢
  replace hc1 : c1.toNat = 39 - L1 := by rw [hc1]; rfl
  ihave Hcur := memBytes_addr (show (sp + 140).toNat = sp.toNat + 140 by simp [UInt32.toNat_add]; omega) $$ Hcur
  ihave Hd1 := memBytes_addr (show (sp + 101).toNat + UInt32.toNat 39 - L1 = sp.toNat + 101 + c1.toNat by
    simp [UInt32.toNat_add]; omega) $$ Hd1
  ihave Hm18 := memBytes_addr (show (sp + 16).toNat + (storeBytes (.i64 r0) 8).length = sp.toNat + 16 + 8 by
    simp [UInt32.toNat_add, storeBytes]; omega) $$ Hm18
  change Iris.ProofMode.Entails' _ (mwpi cfg lim d (fr inst mi x0 x1 1 f sp x5 x6 x7) [] (f902.body.drop 28)
    (Post.mfunc cfg Cg type.results.length Φf))
  rw [← hCRc, ← hCR, ← hACT]
  iapply tRounds cfg lim d type htype inst mi A n g ta hm hd Cg Φf gt N hN x0 x1 x5 x6 x7 hq sp f c1 data vtab idx
    (by rw [hc1, hL1d]) hsp hf hvt a code (ob.take (39 - L1)) m0 (by simp; omega) hm0 Sk Sk' Kw R
  iframe H903 H910 H952 H954 H900 Hi Ha Sw Hg Hcur Hj1 Hd1 Hm0 Hl HF HS
  isplitl [Hc]
  · iapply credits_le
    iframe Hc
    ipureintro; omega
  iunfold KK
  iintro Hc Hg Hb Hs Hl HF HS
  iapply HK $$ Hc Hg Hb [Hs Hm10 Hm18] Hl HF HS
  ihave Hm1 := stk_of n _ 8 _ (by simp [storeBytes]) $$ Hm10
  ihave Hm2 := stk_of n _ 8 _ (by simp [storeBytes]) $$ Hm18
  ihave Hm := stk_join n (sp.toNat + 16) 8 8 $$ [Hm1 Hm2]
  · iframe Hm1; iexact Hm2
  iapply stk_join n sp.toNat 16 16
  iframe Hs Hm


end Tail

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `u128` `lo + 2^64 hi`. -/
def val (lo hi : UInt64) : Nat := lo.toNat + 2 ^ 64 * hi.toNat

/-- The cost of `fmt_u128`, activation and the sink excluded, in `regular_op_cost`s (the end
segment's `101` and the `pad_integral` call included). -/
def cost (lo hi : UInt64) : Nat :=
  (if hi.toNat ≤ 524287 then 25 else 433) + costR1 (val lo hi) + costRounds (val lo hi) + 101

/-- The precondition: `(lo, hi, true, f)`, the 144 bytes of the frame, the table, the `Formatter`. -/
def pre (n g : Nat) (gt : GlobalType) (s : UInt32) (lo hi : UInt64) (ta : Nat) (f data vtab idx : UInt32)
    (a : Nat) (Sk : IProp GF) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i64 lo, .i64 hi, .i32 1, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    n ↦[wms][ 1070974 ] lut ∗ fmtr n ta f data vtab idx a ∗ Sk)

def post (n g : Nat) (gt : GlobalType) (s : UInt32) (ta : Nat) (f data vtab idx : UInt32)
    (a : Nat) (Sk' : IProp GF) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗
    n ↦[wms][ 1070974 ] lut ∗ fmtr n ta f data vtab idx a ∗ Sk')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`core::fmt::num::fmt_u128(lo, hi, true, f)`** (902): the decimal digits of `lo + 2^64 hi`
written through the `Formatter`'s sink in one `write_str` (`sinkSpec`, at the frame's
`sp = s - 144`, on the `(decDigits N).length` bytes at `sp + 101 + 39 - length`). -/
theorem f902_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (lo hi : UInt64) (s f data vtab idx : UInt32) (hs : 144 ≤ s.toNat)
    (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func)
    (Sk Sk' : IProp GF) (Kw : Nat) :
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗
      A 900 ↪[wf] FuncInst.wasm types[56]! inst f900 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      sinkSpec cfg lim (d + 2) inst mi n g gt (s - 144) (UInt32.ofNat (39 - (decDigits (val lo hi)).length))
        data code (decDigits (val lo hi)) Sk Sk' Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f902 Cg
        (pre n g gt s lo hi ta f data vtab idx a Sk)
        (fun _ => cost lo hi * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw)
        (post n g gt s ta f data vtab idx a Sk') := by
  iintro ⟨#H903, #H910, #H952, #H954, #H900, #Hi, #Ha, #Sw⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha954 := hm.funcs 954 (by decide)
  have t8 : types[8]!.params.length = 5 := by rfl
  have hN : val lo hi < 2 ^ 128 := by
    unfold val; have := lo.toNat_lt; have := hi.toNat_lt; omega
  have hlt := s.toNat_lt
  have hlo := lo.toNat_lt
  have h144 : (s - 144).toNat = s.toNat - 144 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  generalize hACT : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, Hs, Hl, HF, HS⟩
  subst hargs
  ihave Hs := stk_addr (show s.toNat - 144 = (s - 144).toNat by omega) $$ Hs
  icases stk_split n (s - 144).toNat 32 112 $$ Hs with ⟨M01, Hs⟩
  icases stk_split n ((s - 144).toNat + 32) 69 43 $$ Hs with ⟨Mid, Buf⟩
  icases stk_split n (s - 144).toNat 16 16 $$ M01 with ⟨M0, M1⟩
  icases stk_split n ((s - 144).toNat + 32 + 69) 39 4 $$ Buf with ⟨Bf, Cu⟩
  iunfold stk at M0 M1 Bf Cu
  icases M0 with ⟨%m0, %hm0, M0⟩
  icases M1 with ⟨%m1, %hm1, M1⟩
  icases Bf with ⟨%bf, %hbf, Bf⟩
  icases Cu with ⟨%cu, %hcu, Cu⟩
  ihave Cu := memBytes_addr (show (s - 144).toNat + 32 + 69 + 39 = (s - 144).toNat + 140 by omega) $$ Cu
  ihave Bf := memBytes_addr (show (s - 144).toNat + 32 + 69 = (s - 144).toNat + 101 by omega) $$ Bf
  unfold cost
  simp only [Nat.add_mul]
  generalize hR1 : costR1 (val lo hi) * cfg.regularOpCost = R1c
  generalize hRR : costRounds (val lo hi) * cfg.regularOpCost = RRc
  simp only [f902]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Cu]
  by_cases hfast : hi.toNat ≤ 524287
  · ------------------------------------------------------------------ the fast division
    have hgt : Numeric.bool (Numeric.irelop64 IRelOp.gt_u hi 524287) = 0 := by
      simp [Numeric.irelop64, Numeric.bool, UInt64.lt_iff_toNat_lt]; omega
    simp only [hfast, ite_true]
    iterate 19 mstep
    have hq : ((lo >>> (19 % 64) ||| hi <<< (45 % 64)) / 19073486328125).toNat + 2 ^ 64 * (0 : UInt64).toNat =
        val lo hi / 10 ^ 19 := by
      have := udiv_fast lo hi hfast; simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero]; exact this
    change Iris.ProofMode.Entails' _ (mwpi (GF := GF) cfg lim d (fr inst mi lo _ 1 f (s - 144) 0 0 0) [] (f902.body.drop 9)
      (Post.mfunc cfg Cg type.results.length _))
    rw [← hR1, ← hRR, ← hACT]
    iapply tR1 cfg lim d type htype inst mi A n g ta hm hd Cg _ gt (val lo hi) hN lo _ 0 0 0
      (by unfold val; omega) hq (s - 144) f data vtab idx (by omega) hf hvt a code bf m0 m1 hbf hm0 hm1
      Sk Sk' Kw R
    iframe H903 H910 H952 H954 H900 Hi Ha Sw Hg Cu Bf M0 M1 Hl HF HS
    isplitl [Hc]
    · iapply credits_le
      iframe Hc
      ipureintro; rw [Nat.add_mul]; omega
    iintro Hc Hg Hb Hs Hl HF HS
    dsimp only
    iframe Hc
    iunfold post
    rw [show s - 144 + 144 = s by simp]
    iframe Hg Hl HF HS
    ihave X := stk_join n (s - 144).toNat 32 69 $$ [Hs Mid]
    · iframe Hs Mid
    ihave Hb := stk_addr (show (s - 144).toNat + 101 = (s - 144).toNat + (32 + 69) by omega) $$ Hb
    ihave X := stk_join n (s - 144).toNat (32 + 69) 43 $$ [X Hb]
    · iframe X Hb
    ihave X := stk_addr (show (s - 144).toNat = s.toNat - 144 by omega) $$ X
    isplitr
    · ipureintro; rfl
    simp only [Nat.reduceAdd]
    iexact X
  · ------------------------------------------------------------------ the slow division
    have hgt : Numeric.bool (Numeric.irelop64 IRelOp.gt_u hi 524287) = 1 := by
      simp [Numeric.irelop64, Numeric.bool, UInt64.lt_iff_toNat_lt]; omega
    simp only [hfast, ite_false]
    have hsp : (s - 144).toNat + 144 ≤ 2 ^ 32 := by omega
    icases stk_split n ((s - 144).toNat + 32) 16 53 $$ Mid with ⟨PB, Mid⟩
    icases stk_split n ((s - 144).toNat + 32 + 16) 16 37 $$ Mid with ⟨PA, Mid⟩
    icases stk_split n ((s - 144).toNat + 32 + 16 + 16) 16 21 $$ Mid with ⟨PD, Mid⟩
    icases stk_split n ((s - 144).toNat + 32 + 16 + 16 + 16) 16 5 $$ Mid with ⟨PC, U5⟩
    iunfold stk at PA PB PC PD
    icases PA with ⟨%pa, %hpa, PA⟩
    icases PB with ⟨%pb, %hpb, PB⟩
    icases PC with ⟨%pc, %hpc, PC⟩
    icases PD with ⟨%pd, %hpd, PD⟩
    ihave PA := memBytes_addr (show (s - 144).toNat + 32 + 16 = (s - 144 + 48).toNat by
      simp [UInt32.toNat_add]; omega) $$ PA
    ihave PB := memBytes_addr (show (s - 144).toNat + 32 = (s - 144 + 32).toNat by
      simp [UInt32.toNat_add]; omega) $$ PB
    ihave PC := memBytes_addr (show (s - 144).toNat + 32 + 16 + 16 + 16 = (s - 144 + 80).toNat by
      simp [UInt32.toNat_add]; omega) $$ PC
    ihave PD := memBytes_addr (show (s - 144).toNat + 32 + 16 + 16 = (s - 144 + 64).toNat by
      simp [UInt32.toNat_add]; omega) $$ PD
    repeat mstep
    mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! (by rfl) inst mi n hn Cg (s - 144 + 48) lo 0
        10779635027931437427 0 pa hpa) using [PA]
    · iunfold FmtMulti3.pre; iframe PA; ipureintro; rfl
    iunfold FmtMulti3.post at HQ
    icases HQ with ⟨%hrs, %a0, %a1, %ha, PA⟩
    subst hrs
    repeat mstep
    mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! (by rfl) inst mi n hn Cg (s - 144 + 32) lo 0
        8507059173023461586 0 pb hpb) using [PB]
    · iunfold FmtMulti3.pre; iframe PB; ipureintro; rfl
    iunfold FmtMulti3.post at HQ
    icases HQ with ⟨%hrs, %b0, %b1, %hb, PB⟩
    subst hrs
    repeat mstep
    mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! (by rfl) inst mi n hn Cg (s - 144 + 80) hi 0
        10779635027931437427 0 pc hpc) using [PC]
    · iunfold FmtMulti3.pre; iframe PC; ipureintro; rfl
    iunfold FmtMulti3.post at HQ
    icases HQ with ⟨%hrs, %c0, %c1, %hc, PC⟩
    subst hrs
    repeat mstep
    mcall (FmtMulti3.f954_spec cfg lim (d + 1) types[8]! (by rfl) inst mi n hn Cg (s - 144 + 64) hi 0
        8507059173023461586 0 pd hpd) using [PD]
    · iunfold FmtMulti3.pre; iframe PD; ipureintro; rfl
    iunfold FmtMulti3.post at HQ
    icases HQ with ⟨%hrs, %d0, %d1, %hdq, PD⟩
    subst hrs
    rw [U128From.u128Bytes, U128From.u128Bytes, U128From.u128Bytes, U128From.u128Bytes]
    icases (memBytes_append (GF := GF) (H := NearState) n _ _ _).1 $$ PA with ⟨PA0, PA8⟩
    icases (memBytes_append (GF := GF) (H := NearState) n _ _ _).1 $$ PB with ⟨PB0, PB8⟩
    icases (memBytes_append (GF := GF) (H := NearState) n _ _ _).1 $$ PC with ⟨PC0, PC8⟩
    icases (memBytes_append (GF := GF) (H := NearState) n _ _ _).1 $$ PD with ⟨PD0, PD8⟩
    simp only [U128From.storeBytes_length]
    repeat mstep
    mstep [PD8]
    repeat mstep
    mstep [PB8]
    repeat mstep
    mstep [PA8]
    repeat mstep
    mstep [PB0]
    repeat mstep
    mstep [PD0]
    repeat mstep
    mstep [PC8]
    repeat mstep
    mstep [PC0]
    simp only [ofNat_decode_i64]
    iterate 23 mstep
    have hhi := hi.toNat_lt
    have ha' : a0.toNat + 2 ^ 64 * a1.toNat = lo.toNat * 10779635027931437427 := by
      rw [ha]; simp only [UInt64.reduceToNat, Nat.mul_zero, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have hb' : b0.toNat + 2 ^ 64 * b1.toNat = lo.toNat * 8507059173023461586 := by
      rw [hb]; simp only [UInt64.reduceToNat, Nat.mul_zero, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have hc' : c0.toNat + 2 ^ 64 * c1.toNat = hi.toNat * 10779635027931437427 := by
      rw [hc]; simp only [UInt64.reduceToNat, Nat.mul_zero, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have hd' : d0.toNat + 2 ^ 64 * d1.toNat = hi.toNat * 8507059173023461586 := by
      rw [hdq]; simp only [UInt64.reduceToNat, Nat.mul_zero, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have hmw := mulhi_words lo hi a0 a1 b0 b1 c0 c1 d0 d1 ha' hb' hc' hd'
    simp only at hmw
    have hq := shr62_words
      (b1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0) a1)).toUInt64 + d0 +
        (c1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0 + c0) (a1 + b0))).toUInt64))
      (d1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u
          (b1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0) a1)).toUInt64 + d0)
          (b1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0) a1)).toUInt64))).toUInt64 +
        (Numeric.bool (Numeric.irelop64 IRelOp.lt_u
          (b1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0) a1)).toUInt64 + d0 +
            (c1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0 + c0) (a1 + b0))).toUInt64))
          (b1 + (Numeric.bool (Numeric.irelop64 IRelOp.lt_u (a1 + b0) a1)).toUInt64 + d0))).toUInt64)
    rw [hmw, Nat.div_div_eq_div_mul, show 2 ^ 128 * 2 ^ 62 = 2 ^ 190 by norm_num,
      magic_div _ (by omega)] at hq
    rw [show (2 : UInt64) = 2 % 64 from rfl, show (62 : UInt64) = 62 % 64 from rfl] at hq
    -- the stack back in one piece for the caller
    ihave PA := U128From.memBytes_join n _ 8 _ _ (U128From.storeBytes_length _ _) $$ [PA0 PA8]
    · iframe PA0 PA8
    ihave PB := U128From.memBytes_join n _ 8 _ _ (U128From.storeBytes_length _ _) $$ [PB0 PB8]
    · iframe PB0 PB8
    ihave PC := U128From.memBytes_join n _ 8 _ _ (U128From.storeBytes_length _ _) $$ [PC0 PC8]
    · iframe PC0 PC8
    ihave PD := U128From.memBytes_join n _ 8 _ _ (U128From.storeBytes_length _ _) $$ [PD0 PD8]
    · iframe PD0 PD8
    ihave PA := stk_of n _ 16 _ (by simp [storeBytes]) $$ PA
    ihave PB := stk_of n _ 16 _ (by simp [storeBytes]) $$ PB
    ihave PC := stk_of n _ 16 _ (by simp [storeBytes]) $$ PC
    ihave PD := stk_of n _ 16 _ (by simp [storeBytes]) $$ PD
    ihave PA := stk_addr (show (s - 144 + 48).toNat = (s - 144).toNat + 32 + 16 by simp [UInt32.toNat_add]; omega) $$ PA
    ihave PB := stk_addr (show (s - 144 + 32).toNat = (s - 144).toNat + 32 by simp [UInt32.toNat_add]; omega) $$ PB
    ihave PC := stk_addr (show (s - 144 + 80).toNat = (s - 144).toNat + 32 + 16 + 16 + 16 by simp [UInt32.toNat_add]; omega) $$ PC
    ihave PD := stk_addr (show (s - 144 + 64).toNat = (s - 144).toNat + 32 + 16 + 16 by simp [UInt32.toNat_add]; omega) $$ PD
    ihave Mid := stk_join n _ 16 5 $$ [PC U5]
    · iframe PC U5
    ihave Mid := stk_join n _ 16 21 $$ [PD Mid]
    · iframe PD Mid
    ihave Mid := stk_join n _ 16 37 $$ [PA Mid]
    · iframe PA Mid
    ihave Mid := stk_join n _ 16 53 $$ [PB Mid]
    · iframe PB Mid
    change Iris.ProofMode.Entails' _ (mwpi (GF := GF) cfg lim d (fr inst mi lo _ 1 f (s - 144) _ _ 0) []
      (f902.body.drop 9) (Post.mfunc cfg Cg type.results.length _))
    rw [← hR1, ← hRR, ← hACT]
    iapply tR1 cfg lim d type htype inst mi A n g ta hm hd Cg _ gt (val lo hi) hN lo _ _ _ 0
      (by unfold val; omega) hq (s - 144) f data vtab idx (by omega) hf hvt a code bf m0 m1 hbf hm0 hm1
      Sk Sk' Kw R
    iframe H903 H910 H952 H954 H900 Hi Ha Sw Hg Cu Bf M0 M1 Hl HF HS
    isplitl [Hc]
    · iapply credits_le
      iframe Hc
      ipureintro; rw [Nat.add_mul]; omega
    iintro Hc Hg Hb Hs Hl HF HS
    dsimp only
    iframe Hc
    iunfold post
    rw [show s - 144 + 144 = s by simp]
    iframe Hg Hl HF HS
    ihave X := stk_join n (s - 144).toNat 32 69 $$ [Hs Mid]
    · iframe Hs Mid
    ihave Hb := stk_addr (show (s - 144).toNat + 101 = (s - 144).toNat + (32 + 69) by omega) $$ Hb
    ihave X := stk_join n (s - 144).toNat (32 + 69) 43 $$ [X Hb]
    · iframe X Hb
    ihave X := stk_addr (show (s - 144).toNat = s.toNat - 144 by omega) $$ X
    isplitr
    · ipureintro; rfl
    simp only [Nat.reduceAdd]
    iexact X

end Spec

end WNear.Binary.FmtU128
