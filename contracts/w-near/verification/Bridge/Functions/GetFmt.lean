import Bridge.Functions.GetSink
import Bridge.Functions.PanicMsgArgs
import Bridge.Functions.PanicFmt

/-!
# `<PanicPayload as BoxMeUp>::get` (826) on `expect_failed`'s payload

```wat
;; 826 get(out, p)                           sp -= 64
[p + 4] = 0 (string: None):
  String::new() (1, 0, 0) at sp + 24;  [sp + 36] := sp + 24
  copy the Arguments at [p] (24 bytes) to sp + 40
  core::fmt::write(sp + 36, 1065680, sp + 40) (872)     ;; the sink 799 (table 165)
  move the String to p + 4  (the old one is None: no drop)
out := (p + 4, 1066400)
```

The formatting is `format_args!("{}", msg)` (`expect_failed`'s), on 826's `String`: a `GetSink.SinkW1`
(`GetSink.sinkW1_get`), written from the empty state: the piece `""`, then `msg` through 880 and 856
(`hypX1`, `PanicMsg.hypX` on `SinkW1`; the lemmas of `PanicDisplay` on `SinkW1`: `sinkW1_piece`,
`f856_w1`, `f880_w1`, `arg880_1`).

`f826_expect`: `PanicWithHook.GetSpec` for 826 on `PanicFmt.fmtPayload` with the `Arguments` of
`expect_failed` (`argsHead`, `expectArgs`) and `getEnv` (the piece `""`, the table entries 195 and
165, the message's bytes, the sink's vtable slot, the heap); after it, the `String` holding `msg` is at
`p + 4` (`GetSink.gsW`, the heap allocated once if `msg ≠ []`) and the rest is given back.
-/

namespace WNear.Binary.GetFmt

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtWriteN (fmtrP Hyp872 argsN costN f872_gen)
open WNear.Binary.FmtStrPad (f856_plain cost856)
open WNear.Binary.PanicDisplay (cost880)
open WNear.Binary.PanicMsg (partX MX XS StX KBX memBytes_two)
open WNear.Binary.GetSink (SinkW1 gsW sinkW1_get getCode costG)
open WNear.Binary.PanicFmt (fmtPayload argsHead expectArgs)
open WNear.Binary.PanicWithHook (GetSpec)
open WNear.Binary.PanicHook (stk4_word stk_split')
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `PanicDisplay`'s writes on a `SinkW1` -/


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `PanicDisplay.sinkW_piece` on `SinkW1` (one more premise: `w = [] ∨ k = 0`). -/
theorem sinkW1_piece (cfg : WasmConfig) (lim : ExecLimits) (D d inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat)
    (sp p k : UInt32) (N : Nat) (w w' sb : List UInt8) (X : IProp GF) (hdD : d ≤ D) (hN : 112 ≤ N)
    (hspN : N ≤ sp.toNat) (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hwB : w.length + k.toNat ≤ B) (hwk : w = [] ∨ k.toNat = 0) (hw' : w' = w ++ sb)
    (hX : X ⊢ n ↦[wms][ p.toNat ] sb ∗ (n ↦[wms][ p.toNat ] sb -∗ X)) :
    SinkW1 cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi code Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (stk n (sp.toNat - N) N ∗ W w ∗ X)))
        (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (stk n (sp.toNat - N) N ∗ W w' ∗ X))) := by
  subst hw'
  iintro #Sw
  iunfold SinkW1 at Sw
  ihave #S := Sw $$ %d %sp %p %k %w %sb %⟨hdD, by omega, hsb, hp, hwB, hwk⟩
  iapply (MFunSpec_frame (GF := GF) (Fr := iprop(stk n (sp.toNat - N) (N - 112) ∗
      (n ↦[wms][ p.toNat ] sb -∗ X)))
    (P := fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb))
    (fun args => by
      iintro ⟨%ha, Hg, Hs, HW, HX⟩
      icases hX $$ HX with ⟨Hp, HX⟩
      icases stkSp (N - 112) 112 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      iframe Hs1 HX Hg HW Hp
      isplitr
      · ipureintro; exact ha
      iapply stkA (by omega) $$ Hs2)
    (fun args rs => by
      iintro ⟨⟨Hs1, HX⟩, %hrs, Hg, Hs2, HW, Hp⟩
      iframe Hg HW
      isplitr
      · ipureintro; exact hrs
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - N) (b := sp.toNat - 112) (k1 := N - 112) (k2 := 112) (by omega) (by omega)
        iframe Hs1 Hs2
      iapply HX $$ Hp))
  iexact S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `PanicDisplay.f856_w` on `SinkW1` (one more premise: `w = [] ∨ k = 0`). -/
theorem f856_w1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 1 ≤ D) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp f data vtab idx p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (hsp : 112 ≤ sp.toNat)
    (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (w sb : List UInt8)
    (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) (hwk : w = [] ∨ k.toNat = 0) :
    inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW1 cfg lim D inst mi n g gt data code W B Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f856 Cg
        (fun args => iprop(⌜args = [.i32 f, .i32 p, .i32 k]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb)))
        (fun _ => cost856 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb))) := by
  iintro ⟨#Hi, #Ha, #Sw⟩
  iunfold SinkW1 at Sw
  ihave #S := Sw $$ %(d + 1) %sp %p %k %w %sb %⟨hdD, hsp, hsb, hp, hwB, hwk⟩
  iapply f856_plain cfg lim d type htype inst mi A n g ta hm hd Cg f data vtab idx p k hf a code
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb)
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb) Kw
  iframe Hi Ha S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `PanicDisplay.f880_w` on `SinkW1` (one more premise: `w = [] ∨ k = 0`). -/
theorem f880_w1 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 2 ≤ D) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp f data vtab idx x p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (hsp : 112 ≤ sp.toNat)
    (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (w sb : List UInt8)
    (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) (hwk : w = [] ∨ k.toNat = 0) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW1 cfg lim D inst mi n g gt data code W B Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f880 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (n ↦[i32][ x.toNat ] p ∗ n ↦[i32][ x.toNat + 4 ] k ∗
            (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))))
        (fun _ => cost880 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (n ↦[i32][ x.toNat ] p ∗ n ↦[i32][ x.toNat + 4 ] k ∗
            (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)))) := by
  iintro ⟨#Hi, #H856, #Ha, #Sw⟩
  ihave #S856 := f856_w1 cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm D (by omega) (by omega) Cg gt sp f
    data vtab idx p k hf hsp a code W B Kw w sb hsb hp hwB hwk $$ [Hi Ha Sw]
  · iframe Hi Ha Sw
  have hn := hm.mem
  have ha856 := hm.funcs 856 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  simp only [cost880]
  generalize hK : cost856 cfg code Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HF, X0, X4, HP⟩
  subst hargs
  simp only [f880]
  repeat mstep
  mstep [X0]
  repeat mstep
  mstep [X4]
  repeat mstep
  mcall S856 using [HF HP]
  · iframe HF HP
  icases HQ with ⟨%hrs, HF, HP⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc HF X0 X4 HP
  ipureintro; rw [htype]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `PanicDisplay.arg880` on `SinkW1` (one more premise: `w = [] ∨ k = 0`). -/
theorem arg880_1 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 2 ≤ D) (hd : d + 2 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp f data vtab idx x p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (N : Nat)
    (hN : 112 ≤ N) (hsp : N ≤ sp.toNat) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat)
    (w w' sb : List UInt8) (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hwB : w.length + k.toNat ≤ B) (hwk : w = [] ∨ k.toNat = 0) (hw' : w' = w ++ sb) (X : IProp GF)
    (hX : X ⊢ n ↦[i32][ x.toNat ] p ∗ n ↦[i32][ x.toNat + 4 ] k ∗ n ↦[wms][ p.toNat ] sb ∗
      (n ↦[i32][ x.toNat ] p -∗ n ↦[i32][ x.toNat + 4 ] k -∗ n ↦[wms][ p.toNat ] sb -∗ X)) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW1 cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      MFunSpec (GF := GF) cfg lim d types[13]! inst mi f880 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtrP n ta f data vtab idx a ∗ (stk n (sp.toNat - N) N ∗ W w ∗ X)))
        (fun _ => cost880 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtrP n ta f data vtab idx a ∗ (stk n (sp.toNat - N) N ∗ W w' ∗ X))) := by
  subst hw'
  iintro ⟨#Hi, #H856, #Ha, #Sw⟩
  ihave #S := f880_w1 cfg lim d types[13]! rfl inst mi A n g ta hm D hdD hd Cg gt sp f data vtab idx x p k hf
    (by omega) a code W B Kw w sb hsb hp hwB hwk $$ [Hi H856 Ha Sw]
  · iframe Hi H856 Ha Sw
  iapply (MFunSpec_frame (GF := GF) (Fr := iprop(stk n (sp.toNat - N) (N - 112) ∗
      (n ↦[i32][ x.toNat ] p -∗ n ↦[i32][ x.toNat + 4 ] k -∗ n ↦[wms][ p.toNat ] sb -∗ X)))
    (fun args => by
      iintro ⟨%ha, Hg, HF, Hs, HW, HX⟩
      icases hX $$ HX with ⟨X0, X4, Hp, HX⟩
      icases stkSp (N - 112) 112 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      iframe Hs1 HX HF X0 X4 Hg HW Hp
      isplitr
      · ipureintro; exact ha
      iapply stkA (by omega) $$ Hs2)
    (fun args rs => by
      iintro ⟨⟨Hs1, HX⟩, %hrs, HF, X0, X4, Hg, Hs2, HW, Hp⟩
      iframe Hg HF HW
      isplitr
      · ipureintro; exact hrs
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - N) (b := sp.toNat - 112) (k1 := N - 112) (k2 := 112) (by omega) (by omega)
        iframe Hs1 Hs2
      iapply HX $$ X0 X4 Hp)) $$ S

/-! ## `format_args!("{}", msg)` on a `SinkW1` -/

/-- The code `format_args!("{}", msg)`'s writes run (persistent). -/
def CX1 (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
    A 880 ↪[wf] FuncInst.wasm types[13]! inst f880 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
    SinkW1 cfg lim D inst mi n g gt data code W B Kw Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (CX1 cfg lim D inst mi A n g gt data a code W B Kw Cg) := by
  unfold CX1; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp872` for `format_args!("{}", msg)` on a `SinkW1`** from the empty state. -/
theorem hypX1 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 3 ≤ D) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s data vtab idx argp x m l e0 : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (w msg : List UInt8) (hs : 160 ≤ s.toNat)
    (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hwB : w.length + msg.length ≤ B) (hw0 : w = []) :
    Hyp872 (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1070628 argp 1 (fun _ => e0)
      (fun _ => 0) (fun _ => x) (fun _ => 195) (fun _ => A 880) (fun _ => f880) a code
      (CX1 cfg lim D inst mi A n g gt data a code W B Kw Cg) (MX n ta A e0 argp x)
      (StX n s W w x m l msg) Kw (cost880 cfg code Kw) (KBX cfg code Kw) := by
  have hlt := s.toNat_lt
  have hs48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, hs48]; omega
  have hj1 : ∀ j, j < (1 : UInt32).toNat → j = 0 := fun j hj => by
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MX at H
    icases H with ⟨⟨P0, P4⟩, Q⟩
    iframe P0 P4
    iintro ⟨P0, P4⟩
    iunfold MX
    iframe P0 P4 Q
  · intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MX at H
    icases H with ⟨P, ⟨Q0, Q4, Qt⟩⟩
    iframe Q0 Q4 Qt
    iintro ⟨Q0, Q4, Qt⟩
    iunfold MX
    iframe P Q0 Q4 Qt
  · iintro #C
    iunfold CX1 at C
    icases C with ⟨#Hi, -, -, #Ha, -⟩
    iframe Hi Ha
  · intro j hj
    rcases hj1 j hj
    simp only [StX, Nat.reduceMul]
    iintro #C
    iunfold CX1 at C
    icases C with ⟨-, -, -, -, #Sw⟩
    iapply sinkW1_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) e0 0 112
      (w ++ partX msg 0) (w ++ partX msg 1) [] _ (by omega) le_rfl (by omega) rfl (by have := e0.toNat_lt; simp; omega)
      (by simp [partX]; omega) (Or.inr rfl) (by simp [partX])
      (by
        iintro H
        iframe H
        isplitr
        · iapply FmtString.memBytes_nil
        iintro -; iempintro)
    iexact Sw
  · intro j hj
    rcases hj1 j hj
    iintro #C
    iunfold CX1 at C
    icases C with ⟨-, -, #H880, -⟩
    iexact H880
  · intro j hj
    rcases hj1 j hj
    simp only [StX, Nat.reduceMul, Nat.reduceAdd]
    iintro #C
    iunfold CX1 at C
    icases C with ⟨#Hi, #H856, -, #Ha, #Sw⟩
    simp only [partX, List.append_nil]
    iapply arg880_1 cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48) (s - 48 + 8)
      data vtab idx x m l (by omega) 112 le_rfl (by omega) a code W B Kw w (w ++ msg) msg hmsg hml
      (by omega) (Or.inl hw0) rfl (XS n x m l msg)
      (by
        iintro H
        iunfold XS at H
        icases H with ⟨X0, X4, Hm⟩
        iframe X0 X4 Hm
        iintro X0 X4 Hm
        iunfold XS
        iframe X0 X4 Hm)
    iframe Hi H856 Ha Sw
  · intro j hj
    rcases hj1 j hj
    unfold KBX; omega

/-! ## `gsW`'s words -/

/-- `gsW`'s three words, and `gsW` at any other address holding them. -/
theorem gsW_cells (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (v idx : UInt32) (ta a578 : Nat)
    (w : List UInt8) :
    gsW (GF := GF) n maxP hl live F v idx ta a578 w ⊢ ∃ x y z : UInt32,
      n ↦[i32][ v.toNat ] x ∗ n ↦[i32][ v.toNat + 4 ] y ∗ n ↦[i32][ v.toNat + 8 ] z ∗
      (∀ v' : UInt32, n ↦[i32][ v'.toNat ] x -∗ n ↦[i32][ v'.toNat + 4 ] y -∗ n ↦[i32][ v'.toNat + 8 ] z -∗
        gsW n maxP hl live F v' idx ta a578 w) := by
  iintro H
  iunfold gsW at H
  by_cases hw : w = []
  · simp only [hw, ↓reduceIte]
    icases H with ⟨Hvt, V0, V4, V8, Hinv⟩
    iexists 1, 0, 0
    iframe V0 V4 V8
    iintro %v' V0 V4 V8
    iunfold gsW
    simp only [↓reduceIte]
    iframe Hvt V0 V4 V8 Hinv
  · simp only [hw, ↓reduceIte]
    icases H with ⟨Hvt, %q, %c, %hl', %tail, %hx, V0, V4, V8, Hb, Hinv⟩
    iexists q, c, UInt32.ofNat w.length
    iframe V0 V4 V8
    iintro %v' V0 V4 V8
    iunfold gsW
    simp only [hw, ↓reduceIte]
    iframe Hvt
    iexists q, c, hl', tail
    iframe V0 V4 V8 Hb Hinv
    ipureintro; exact hx



/-! ## 826 -/

/-- What 826 reads besides the payload, the `Arguments`' header and the heap: the piece `""` at
1070628, the table entries 195 (880) and 165 (799, the sink's `write_str`), the message's bytes, the
sink's vtable slot. -/
def getData (n ta : Nat) (A : Nat → Nat) (m : UInt32) (msg : List UInt8) : IProp GF :=
  iprop((n ↦[i32][ (1070628 : UInt32).toNat + 8 * 0 ] 1067136 ∗
      n ↦[i32][ (1070628 : UInt32).toNat + 8 * 0 + 4 ] 0) ∗
    ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ n ↦[wms][ m.toNat ] msg ∗
    (n ↦[i32][ (1065680 : UInt32).toNat + 12 ] 165 ∗ ta ↦[wt][ (165 : UInt32).toNat ] Ref.func (A 799)))

/-- The code 826 runs (persistent). -/
def code826 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(getCode n maxP inst mi A ∗ A 799 ↪[wf] FuncInst.wasm types[15]! inst f799 ∗
    A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
    A 880 ↪[wf] FuncInst.wasm types[13]! inst f880)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (code826 (GF := GF) n maxP inst mi A) := by
  unfold code826; infer_instance

/-- 826's cost on `expect_failed`'s payload. -/
noncomputable def cost826 (cfg : WasmConfig) (F B : Nat) : Nat :=
  250 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
    costN cfg f799 (costG cfg F B) (KBX cfg f799 (costG cfg F B)) 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`<PanicPayload as BoxMeUp>::get(out, p0)`** (826) on `PanicPayload { inner: a, string: None }`,
`a` `expect_failed`'s `format_args!("{}", (m, l))` in its frame `s8`: the message formatted into a
fresh `String`, moved to `p0 + 4`; `(p0 + 4, 1066400)` at `out`. -/
theorem f826_expect (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 5 ≤ D) (hD : D + 9 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s p0 s8 m l idx : UInt32) (S : Nat) (hS : 224 ≤ S) (hsS : S ≤ s.toNat)
    (hs2 : s.toNat + 16 ≤ 2 ^ 32) (hp0 : p0.toNat + 16 ≤ 2 ^ 32) (hs8 : s8.toNat + 56 ≤ 2 ^ 32)
    (msg : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F B : Nat) (hF : 1 ≤ F) (hB : 1 ≤ B) (hB2 : B ≤ 65000)
    (hmB : msg.length ≤ B) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hroom : hl + 2 * 65536 ≤ 2 ^ 32)
    (hmax : hl + 65536 ≤ maxP * 65536) :
    code826 n maxP inst mi A ⊢
      GetSpec (GF := GF) cfg lim d inst mi Cg n g gt s p0 (p0 + 4) 1066400 S f826
        iprop(fmtPayload n p0 (s8 + 16) ∗ (argsHead n (s8 + 16) 1 1 ∗ (expectArgs n s8 m l ∗
          (getData n ta A m msg ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F))))
        iprop((n ↦[i32][ p0.toNat ] (s8 + 16) ∗ gsW n maxP hl live F (p0 + 4) idx ta (A 578) msg) ∗
          (argsHead n (s8 + 16) 1 1 ∗ (expectArgs n s8 m l ∗ getData n ta A m msg)))
        (cost826 cfg F B) := by
  have hlt := s.toNat_lt
  have h64 : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hv : (s - 64 + 24).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h64]; omega
  have hdd : (s - 64 + 36).toNat = s.toNat - 28 := by simp [UInt32.toNat_add, h64]; omega
  have har : (s - 64 + 40).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h64]; omega
  have ha : (s8 + 16).toNat = s8.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have hx : (s8 + 8).toNat = s8.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have hap : (s8 + 40).toNat = s8.toNat + 40 := by simp [UInt32.toNat_add]; omega
  have hp4 : (p0 + 4).toNat = p0.toNat + 4 := by simp [UInt32.toNat_add]; omega
  have h112 : (s - 64 - 48).toNat = s.toNat - 112 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  iintro #Hc0
  ihave #Hc1 := Hc0
  iunfold code826 at Hc1
  icases Hc1 with ⟨#Hgc, #H799, #H872, #H856, #H880⟩
  ihave #Hgc' := Hgc
  iunfold getCode at Hgc'
  icases Hgc' with ⟨#H310c, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha872 := hm.funcs 872 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  ihave #Sw := sinkW1_get (GF := GF) cfg lim inst mi A n g ta hm Cg gt maxP hl live F B (s - 64 + 24) idx
    (s - 64 + 36) D hD hF hB hB2 (by omega) hl0 hl1 hroom hmax $$ [Hgc H799]
  · iframe Hgc H799
  ihave #CXh : CX1 cfg lim D inst mi A n g gt (s - 64 + 36) (A 799) f799
      (fun w => iprop(n ↦[i32][ (s - 64 + 36).toNat ] (s - 64 + 24) ∗
        gsW n maxP hl live F (s - 64 + 24) idx ta (A 578) w)) B (costG cfg F B) Cg $$ [Hi H856 H880 H799 Sw]
  · iunfold CX1; iframe Hi H856 H880 H799 Sw
  have S872 := f872_gen (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 64)
    (s - 64 + 36) 1065680 (s - 64 + 40) 1070628 (s8 + 40) 165 1 (by decide) (by omega) (by rw [har]; omega) (by simp)
    (by simp only [UInt32.reduceToNat]; rw [hap]; omega) (fun _ => 1067136) (fun _ => 0) (fun _ => s8 + 8) (fun _ => 195) (fun _ => A 880)
    (fun _ => f880) (A 799) f799
    (CX1 cfg lim D inst mi A n g gt (s - 64 + 36) (A 799) f799
      (fun w => iprop(n ↦[i32][ (s - 64 + 36).toNat ] (s - 64 + 24) ∗
        gsW n maxP hl live F (s - 64 + 24) idx ta (A 578) w)) B (costG cfg F B) Cg)
    (MX n ta A 1067136 (s8 + 40) (s8 + 8))
    (StX n (s - 64) (fun w => iprop(n ↦[i32][ (s - 64 + 36).toNat ] (s - 64 + 24) ∗
        gsW n maxP hl live F (s - 64 + 24) idx ta (A 578) w)) [] (s8 + 8) m l msg)
    (costG cfg F B) (cost880 cfg f799 (costG cfg F B)) (KBX cfg f799 (costG cfg F B))
    (hypX1 cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 64) (s - 64 + 36) 1065680 165
      (s8 + 40) (s8 + 8) m l 1067136 (A 799) f799 _ B (costG cfg F B) [] msg (by omega) (by omega) hmsg hml
      (by simpa using hmB) rfl)
  rw [show 2 * (1 : UInt32).toNat = 2 from rfl, show (1 : UInt32).toNat = 1 from rfl] at S872
  unfold GetSpec
  simp only [cost826]
  generalize hK : costN cfg f799 (costG cfg F B) (KBX cfg f799 (costG cfg F B)) 1 = K at S872 ⊢
  ihave #S872' := S872 $$ CXh
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hout, HPay, HA, HE, HD, Hvt, Hinv⟩
  subst hargs
  iunfold fmtPayload at HPay
  icases HPay with ⟨P0, P4, P8⟩
  iunfold argsHead at HA
  icases HA with ⟨A4, A20⟩
  iunfold expectArgs at HE
  icases HE with ⟨E8, E12, E16, E24, E32, E40, E44, %w28, E28⟩
  iunfold getData at HD
  icases HD with ⟨HPc, T195, Hm, ⟨V165, T165⟩⟩
  -- the stack: S - 224 unused, 160 for 872 and its writes, 826's frame of 64
  icases stk_split' n _ S (S - 64) 64 (by omega) $$ Hs with ⟨Lo, Fr⟩
  icases stk_split' n _ (S - 64) (S - 224) 160 (by omega) $$ Lo with ⟨Lo0, L160⟩
  ihave Fr := stk_addr (show s.toNat - S + (S - 64) = (s - 64).toNat by omega) $$ Fr
  icases stk_split' n _ 64 8 56 rfl $$ Fr with ⟨X0, Fr⟩
  icases stk_split' n _ 56 8 48 rfl $$ Fr with ⟨C8, Fr⟩
  icases stk_split' n _ 48 4 44 rfl $$ Fr with ⟨W16, Fr⟩
  icases stk_split' n _ 44 4 40 rfl $$ Fr with ⟨X20, Fr⟩
  icases stk_split' n _ 40 8 32 rfl $$ Fr with ⟨V24, Fr⟩
  icases stk_split' n _ 32 4 28 rfl $$ Fr with ⟨V32, Fr⟩
  icases stk_split' n _ 28 4 24 rfl $$ Fr with ⟨D36, Fr⟩
  icases stk_split' n _ 24 8 16 rfl $$ Fr with ⟨C40, Fr⟩
  icases stk_split' n _ 16 8 8 rfl $$ Fr with ⟨C48, C56⟩
  icases stk4_word n _ $$ W16 with ⟨%o16, W16⟩
  icases stk4_word n _ $$ V32 with ⟨%o32, V32⟩
  icases stk4_word n _ $$ D36 with ⟨%o36, D36⟩
  iunfold stk at C8 V24 C40 C48 C56
  icases C8 with ⟨%c8, %hc8, C8⟩
  icases V24 with ⟨%c24, %hc24, V24⟩
  icases C40 with ⟨%c40, %hc40, C40⟩
  icases C48 with ⟨%c48, %hc48, C48⟩
  icases C56 with ⟨%c56, %hc56, C56⟩
  icases stk_split' n _ 8 4 4 rfl $$ Hout with ⟨O0, O4⟩
  icases stk4_word n _ $$ O0 with ⟨%q0, O0⟩
  icases stk4_word n _ $$ O4 with ⟨%q4, O4⟩
  icases stk_split' n _ 8 4 4 rfl $$ P8 with ⟨P8, P12⟩
  icases stk4_word n _ $$ P8 with ⟨%r8, P8⟩
  icases stk4_word n _ $$ P12 with ⟨%r12, P12⟩
  -- the `Arguments` as three double words
  ihave HA0 := (memBytes_two n (s8 + 16).toNat 1070628 1).2 $$ [E16 A4]
  · iframe A4; iapply memBytes_addr _ $$ E16; omega
  ihave HA8 := (memBytes_two n ((s8 + 16 + 8).toNat) 0 w28).2 $$ [E24 E28]
  · isplitl [E24]; · iapply memBytes_addr _ $$ E24; simp [UInt32.toNat_add]; omega
    iapply memBytes_addr _ $$ E28; simp [UInt32.toNat_add]; omega
  ihave HA16 := (memBytes_two n ((s8 + 16 + 16).toNat) (s8 + 40) 1).2 $$ [E32 A20]
  · isplitl [E32]; · iapply memBytes_addr _ $$ E32; simp [UInt32.toNat_add]; omega
    iapply memBytes_addr _ $$ A20; simp [UInt32.toNat_add]; omega
  ihave C56 := memBytes_addr (show (s - 64).toNat + 8 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8 = (s - 64 + 40 + 16).toNat by
    simp [UInt32.toNat_add, h64]; omega) $$ C56
  ihave C48 := memBytes_addr (show (s - 64).toNat + 8 + 8 + 4 + 4 + 8 + 4 + 4 + 8 = (s - 64 + 40 + 8).toNat by
    simp [UInt32.toNat_add, h64]; omega) $$ C48
  ihave C40 := memBytes_addr (show (s - 64).toNat + 8 + 8 + 4 + 4 + 8 + 4 + 4 = (s - 64).toNat + 40 by
    omega) $$ C40
  ihave V24 := memBytes_addr (show (s - 64).toNat + 8 + 8 + 4 + 4 = (s - 64).toNat + 24 by omega) $$ V24
  ihave V32 := memBytes_addr (show (s - 64).toNat + 8 + 8 + 4 + 4 + 8 = (s - 64).toNat + 32 by omega) $$ V32
  ihave D36 := memBytes_addr (show (s - 64).toNat + 8 + 8 + 4 + 4 + 8 + 4 = (s - 64 + 36).toNat by omega) $$ D36
  simp only [f826]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [P4]
  repeat mstep
  mstep [P0]
  repeat mstep
  mstep [V32]
  repeat mstep
  mstep [V24]
  repeat mstep
  mstep [D36]
  repeat mstep
  mstep [HA16]
  mstep [C56]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  mstep [HA8]
  mstep [C48]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  mstep [HA0]
  mstep [C40]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  -- the call: 872 on the copy
  rw [show storeBytes (.i64 1) 8 = bytes32 1 ++ bytes32 0 by decide]
  icases (memBytes_two n _ 1 0).1 $$ V24 with ⟨V0, V4⟩
  icases (memBytes_two n _ 1070628 1).1 $$ C40 with ⟨Q0, Q4⟩
  icases (memBytes_two n _ 0 w28).1 $$ C48 with ⟨Q8, Q12⟩
  icases (memBytes_two n _ (s8 + 40) 1).1 $$ C56 with ⟨Q16, Q20⟩
  icases stk_split' n _ 160 112 48 rfl $$ L160 with ⟨L112, L48⟩
  mcall S872' using [Hg L48 Q0 Q4 Q8 Q16 Q20 HPc E40 E44 T195 V165 T165 L112 D36 Hvt V0 V4 V32 Hinv E8 E12 Hm]
  · iframe Hg V165 T165
    isplitl [L48]; · iapply stk_addr _ $$ L48; omega
    isplitl [Q0 Q4 Q8 Q16 Q20]
    · iunfold argsN
      rw [har]
      isplitl [Q0]; · iapply memBytes_addr _ $$ Q0; omega
      isplitl [Q4]; · iapply memBytes_addr _ $$ Q4; omega
      isplitl [Q8]; · iapply memBytes_addr _ $$ Q8; simp [UInt32.toNat_add, h64]; omega
      isplitl [Q16]; · iapply memBytes_addr _ $$ Q16; simp [UInt32.toNat_add, h64]; omega
      iapply memBytes_addr _ $$ Q20; simp [UInt32.toNat_add, h64]; omega
    isplitl [HPc E40 E44 T195]
    · iunfold MX
      simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]
      iframe HPc T195
      rw [hap]
      iframe E40 E44
    iunfold StX
    isplitl [L112]; · iapply stk_addr _ $$ L112; omega
    isplitl [D36 Hvt V0 V4 V32 Hinv]
    · simp only [partX, List.append_nil]
      iframe D36
      iunfold gsW
      simp only [↓reduceIte]
      iframe Hvt Hinv
      isplitl [V0]; · iapply memBytes_addr _ $$ V0; omega
      isplitl [V4]; · iapply memBytes_addr _ $$ V4; simp [bytes32]; omega
      iapply memBytes_addr _ $$ V32; omega
    iunfold XS
    rw [hx]
    iframe E8 E12 Hm
  icases HQ with ⟨%hrs, Hg, L48, HA, HM, V165, T165, HSt⟩
  subst hrs
  mcredits (100 * cfg.regularOpCost + R)
  repeat mstep
  iunfold StX at HSt
  icases HSt with ⟨L112, ⟨D36, HGs⟩, HXS⟩
  simp only [partX, List.nil_append]
  icases gsW_cells n maxP hl live F (s - 64 + 24) idx ta (A 578) msg $$ HGs with ⟨%x, %y, %z, G0, G4, G8, Gw⟩
  ihave G8 := memBytes_addr (show (s - 64 + 24).toNat + 8 = (s - 64).toNat + 32 by omega) $$ G8
  ihave W16 := memBytes_addr (show (s - 64).toNat + 8 + 8 = (s - 64 + 8 + 8).toNat by
    simp [UInt32.toNat_add, h64]; omega) $$ W16
  mstep [G8]
  mstep [W16]
  repeat mstep
  ihave GV := (memBytes_two n ((s - 64).toNat + 24) x y).2 $$ [G0 G4]
  · isplitl [G0]; · iapply memBytes_addr _ $$ G0; omega
    iapply memBytes_addr _ $$ G4; omega
  mstep [GV]
  mstep [C8]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  mstep [P4]
  repeat mstep
  ihave PV := (memBytes_two n (p0 + 4).toNat 0 r8).2 $$ [P4 P8]
  · isplitl [P4]; · iapply memBytes_addr _ $$ P4; omega
    iapply memBytes_addr _ $$ P8; omega
  mstep [C8]
  mstep [PV]
  rw [ResultExpect.bytes64_decode _ (by simp [bytes32])]
  repeat mstep
  ihave P12 := memBytes_addr (show p0.toNat + 8 + 4 = (p0 + 4 + 8).toNat by simp [UInt32.toNat_add]; omega) $$ P12
  mstep [W16]
  mstep [P12]
  repeat mstep
  ihave O4 := memBytes_addr (show s.toNat + 8 + 4 = (s + 8).toNat + 4 by simp [UInt32.toNat_add]; omega) $$ O4
  ihave O0 := memBytes_addr (show s.toNat + 8 = (s + 8).toNat by simp [UInt32.toNat_add]; omega) $$ O0
  mstep [O4]
  repeat mstep
  mstep [O0]
  repeat mstep
  rw [show s - 64 + 64 = s by simp]
  mstep [Hg]
  mcredits R
  icases (memBytes_two n _ x y).1 $$ PV with ⟨PV0, PV4⟩
  ihave P12 := memBytes_addr (show (p0 + 4 + 8).toNat = (p0 + 4).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ P12
  ihave HGs := Gw $$ %(p0 + 4) PV0 PV4 P12
  iframe Hc Hg P0 HGs
  iunfold argsN at HA
  icases HA with ⟨Q0, Q4, Q8, Q16, Q20⟩
  iunfold MX at HM
  icases HM with ⟨HPc, E40, E44, T195⟩
  iunfold XS at HXS
  icases HXS with ⟨E8, E12, Hm⟩
  isplitl [Lo0 L112 L48 X0 C8 W16 X20 GV G8 D36 Q0 Q4 Q8 Q12 Q16 Q20]
  · ihave C40 := (memBytes_two n ((s - 64).toNat + 40) 1070628 1).2 $$ [Q0 Q4]
    · isplitl [Q0]; · iapply memBytes_addr _ $$ Q0; omega
      iapply memBytes_addr _ $$ Q4; omega
    ihave C48 := (memBytes_two n ((s - 64).toNat + 48) 0 w28).2 $$ [Q8 Q12]
    · isplitl [Q8]; · iapply memBytes_addr _ $$ Q8; simp [UInt32.toNat_add, h64]; omega
      iapply memBytes_addr _ $$ Q12; simp [UInt32.toNat_add, h64]; omega
    ihave C56 := (memBytes_two n ((s - 64).toNat + 56) (s8 + 40) 1).2 $$ [Q16 Q20]
    · isplitl [Q16]; · iapply memBytes_addr _ $$ Q16; simp [UInt32.toNat_add, h64]; omega
      iapply memBytes_addr _ $$ Q20; simp [UInt32.toNat_add, h64]; omega
    ihave C8 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C8
    ihave GV := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ GV
    ihave C40 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C40
    ihave C48 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C48
    ihave C56 := FmtU128.stk_of n _ 8 _ (by simp [bytes32]) $$ C56
    ihave W16 := stk_word n _ _ $$ W16
    ihave G8 := stk_word n _ _ $$ G8
    ihave D36 := stk_word n _ _ $$ D36
    ihave H := stkJ (a := (s - 64).toNat + 48) (b := (s - 64).toNat + 56) (k1 := 8) (k2 := 8) (k := 16) rfl rfl
      $$ [C48 C56]
    · iframe C48 C56
    ihave H := stkJ (a := (s - 64).toNat + 40) (b := (s - 64).toNat + 48) (k1 := 8) (k2 := 16) (k := 24) rfl rfl
      $$ [C40 H]
    · iframe C40 H
    ihave H := stkJ (a := (s - 64).toNat + 36) (b := (s - 64).toNat + 40) (k1 := 4) (k2 := 24) (k := 28) rfl rfl
      $$ [D36 H]
    · iframe H; iapply stk_addr _ $$ D36; omega
    ihave H := stkJ (a := (s - 64).toNat + 32) (b := (s - 64).toNat + 36) (k1 := 4) (k2 := 28) (k := 32) rfl rfl
      $$ [G8 H]
    · iframe G8 H
    ihave H := stkJ (a := (s - 64).toNat + 24) (b := (s - 64).toNat + 32) (k1 := 8) (k2 := 32) (k := 40) rfl rfl
      $$ [GV H]
    · iframe GV H
    ihave H := stkJ (a := (s - 64).toNat + 20) (b := (s - 64).toNat + 24) (k1 := 4) (k2 := 40) (k := 44) rfl rfl
      $$ [X20 H]
    · iframe H; iapply stk_addr _ $$ X20; omega
    ihave H := stkJ (a := (s - 64).toNat + 16) (b := (s - 64).toNat + 20) (k1 := 4) (k2 := 44) (k := 48) rfl rfl
      $$ [W16 H]
    · iframe H; iapply stk_addr _ $$ W16; simp [UInt32.toNat_add, h64]; omega
    ihave H := stkJ (a := (s - 64).toNat + 8) (b := (s - 64).toNat + 16) (k1 := 8) (k2 := 48) (k := 56) rfl rfl
      $$ [C8 H]
    · iframe C8 H
    ihave H := stkJ (a := (s - 64).toNat) (b := (s - 64).toNat + 8) (k1 := 8) (k2 := 56) (k := 64) rfl rfl
      $$ [X0 H]
    · iframe X0 H
    ihave L := stkJ (a := (s - 64).toNat - 160) (b := (s - 64).toNat - 48) (k1 := 112) (k2 := 48) (k := 160)
      (by omega) rfl $$ [L112 L48]
    · iframe L48; iapply stk_addr _ $$ L112; omega
    ihave L := stkJ (a := s.toNat - S) (b := (s - 64).toNat - 160) (k1 := S - 224) (k2 := 160) (k := S - 64)
      (by omega) (by omega) $$ [Lo0 L]
    · iframe Lo0 L
    iapply stkJ (a := s.toNat - S) (b := (s - 64).toNat) (k1 := S - 64) (k2 := 64) (k := S) (by omega) (by omega)
    iframe L H
  isplitl [O0]; · iapply memBytes_addr _ $$ O0; simp [UInt32.toNat_add]; omega
  isplitl [O4]; · iapply memBytes_addr _ $$ O4; simp [UInt32.toNat_add]; omega
  icases (memBytes_two n _ 1070628 1).1 $$ HA0 with ⟨E16, A4⟩
  icases (memBytes_two n _ 0 w28).1 $$ HA8 with ⟨E24, E28⟩
  icases (memBytes_two n _ (s8 + 40) 1).1 $$ HA16 with ⟨E32, A20⟩
  isplitl [A4 A20]
  · iunfold argsHead
    iframe A4
    iapply memBytes_addr _ $$ A20; simp [UInt32.toNat_add]; omega
  isplitl [E8 E12 E16 E24 E28 E32 E40 E44]
  · iunfold expectArgs
    rw [hx] at *
    rw [hap] at *
    iframe E8 E12 E40 E44
    isplitl [E16]; · iapply memBytes_addr _ $$ E16; omega
    isplitl [E24]; · iapply memBytes_addr _ $$ E24; simp [UInt32.toNat_add]; omega
    isplitl [E32]; · iapply memBytes_addr _ $$ E32; simp [UInt32.toNat_add]; omega
    iexists w28
    iapply memBytes_addr _ $$ E28; simp [UInt32.toNat_add]; omega
  iunfold getData
  simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]
  iframe HPc T195 Hm V165 T165

end Spec

end WNear.Binary.GetFmt
