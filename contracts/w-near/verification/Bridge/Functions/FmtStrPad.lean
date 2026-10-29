import Bridge.Functions.FmtWriteN
import Bridge.Functions.SerdeAccountId
import Binary.Code.Part01
import Binary.Code.Part15
import Binary.Code.Part20

/-!
# `Formatter::pad` (856) without width or precision, `<str as Display>::fmt` (923) and
`<String as Display>::fmt` (179) (M8)

`format!("…{}…", s)` with `s : String` formats through table entry 6, 179:

```
179 <String as Display>::fmt(s, f)   sp -= 16; (ptr, len) = s.deref() (779) at sp + 8;
                                     r = <str as Display>::fmt(ptr, len, f) (923); sp += 16; r
923 <str as Display>::fmt(p, k, f)   Formatter::pad(f, p, k) (856)
856 Formatter::pad(f, p, k)          width (f + 8) None and precision (f + 16) None
                                     ⇒ return (f.vtable.write_str)(f.data, p, k)   (call_indirect 15)
```

The `Formatter` is `FmtWriteN.fmtrP`: `pad` reads the width and precision tags and the sink.
Each spec is parametric in the sink's `write_str` (code `a`, `[data, p, k]`, `Pw → Qw`, `Ok`).
Costs (`regular_op_cost`s, activations of 856/923 included in the callers' counts as usual):
856 `21` plus the `call_indirect`, the sink's activation and `Kw`; 923 `5 + cost856`;
179 `24 + 12 (779) + cost923`.
-/

namespace WNear.Binary.FmtStrPad

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtWriteN (fmtrP)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.AllocNewCell (memBytes_addr)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of `pad` (856) on the plain path, the activation excluded. -/
def cost856 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  30 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw

theorem act3 (c : Nat) (code : Func) (a b e : UInt32) :
    activationGas c (entryLocals code [.i32 a, .i32 b, .i32 e]) =
      activationGas c (entryLocals code [.i32 0, .i32 0, .i32 0]) := by
  simp [activationGas, entryLocals]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Formatter::pad(f, p, k)`** (856) with no width and no precision: the `k` bytes at `p`
written with the sink's `write_str`, its result returned. -/
theorem f856_plain (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (f data vtab idx p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (a : Nat) (code : Func) (Pw Qw : IProp GF)
    (Kw : Nat) :
    inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      MFunSpec cfg lim (d + 1) types[15]! inst mi code Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ Pw)) (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Qw))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f856 Cg
        (fun args => iprop(⌜args = [.i32 f, .i32 p, .i32 k]⌝ ∗ fmtrP n ta f data vtab idx a ∗ Pw))
        (fun _ => cost856 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗ Qw)) := by
  iintro ⟨#Hi, #Ha, #Sw⟩
  have hn := hm.mem
  have hta := hm.table
  have hty : types[15]! = mi.types[15]! := by rw [hm.types]
  simp only [cost856]
  generalize hact : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HF, HP⟩
  subst hargs
  iunfold fmtrP, fmtr at HF
  icases HF with ⟨⟨F0, F8, F24, F28, V12, Ht⟩, F16⟩
  simp only [f856]
  repeat mstep
  mstep [F16]
  repeat mstep
  mstep [F8]
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [F28]
  mstep [V12]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 p, Value.i32 k, Value.i32 idx] =
    [Value.i32 data, Value.i32 p, Value.i32 k] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 7 * cfg.regularOpCost + R) 15 0 ta idx a types[15]! inst mi code
    [.i32 data, .i32 p, .i32 k] _ (fun _ => Kw) _ hta hty rfl (by omega)
  rw [act3, hact]
  isplitl [Hc]
  · iapply credits_le
    isplitl [Hc]
    · iexact Hc
    · ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact Sw
  isplitl [HP]
  · iframe HP
    ipureintro; rfl
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mstep_post
  repeat mstep
  mcredits R
  iframe Hc HQ
  isplitr
  · ipureintro; rw [htype]; rfl
  iunfold fmtrP, fmtr
  iframe F0 F8 F24 F28 V12 Ht F16

/-- The cost of `<str as Display>::fmt` (923), the activation excluded. -/
noncomputable def cost923 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  6 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f856 [.i32 0, .i32 0, .i32 0]) +
    cost856 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<str as Display>::fmt(p, k, f)`** (923): `pad(f, p, k)`. -/
theorem f923_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (f data vtab idx p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (a : Nat) (code : Func) (Pw Qw : IProp GF)
    (Kw : Nat) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
      a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      MFunSpec cfg lim (d + 2) types[15]! inst mi code Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ Pw)) (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Qw))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f923 Cg
        (fun args => iprop(⌜args = [.i32 p, .i32 k, .i32 f]⌝ ∗ fmtrP n ta f data vtab idx a ∗ Pw))
        (fun _ => cost923 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗ Qw)) := by
  iintro ⟨#Hi, #H856, #Ha, #Sw⟩
  ihave #S856 := f856_plain cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg f data vtab idx
    p k hf a code Pw Qw Kw $$ [Hi Ha Sw]
  · iframe Hi Ha Sw
  have hn := hm.mem
  have ha856 := hm.funcs 856 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  simp only [cost923]
  generalize hK : cost856 cfg code Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HF, HP⟩
  subst hargs
  simp only [f923]
  repeat mstep
  mcall S856 using [HF HP]
  · iframe HF HP
  icases HQ with ⟨%hrs, HF, HQ⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc HF HQ
  ipureintro; rw [htype]; rfl

/-- A `String` at `sv`: `(ptr, cap, len)`. -/
def strW (n : Nat) (sv ptr cap len : UInt32) : IProp GF :=
  iprop(n ↦[i32][ sv.toNat ] ptr ∗ n ↦[i32][ sv.toNat + 4 ] cap ∗ n ↦[i32][ sv.toNat + 8 ] len)

/-- The cost of `<String as Display>::fmt` (179), the activation excluded. -/
noncomputable def cost179 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  26 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f779 [.i32 0, .i32 0]) +
    12 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f923 [.i32 0, .i32 0, .i32 0]) +
    cost923 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<String as Display>::fmt(sv, f)`** (179, table entry 6): the `len` bytes of the `String` at
`sv` written with the sink's `write_str` through `pad`, from 16 bytes of stack below `sp`. -/
theorem f179_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp sv ptr cap len f data vtab idx : UInt32) (hsp : 16 ≤ sp.toNat)
    (hf : f.toNat + 32 ≤ 2 ^ 32) (a : Nat) (code : Func) (Pw Qw : IProp GF) (Kw : Nat) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
      A 923 ↪[wf] FuncInst.wasm types[15]! inst f923 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      MFunSpec cfg lim (d + 3) types[15]! inst mi code Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 ptr, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ Pw))
        (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ Qw))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f179 Cg
        (fun args => iprop(⌜args = [.i32 sv, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ strW n sv ptr cap len ∗ fmtrP n ta f data vtab idx a ∗ Pw))
        (fun _ => cost179 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ strW n sv ptr cap len ∗ fmtrP n ta f data vtab idx a ∗ Qw)) := by
  iintro ⟨#Hi, #H856, #H923, #H779, #Ha, #Sw⟩
  ihave #S923 := f923_spec cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg f data vtab idx
    ptr len hf a code iprop(g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ Pw) iprop(g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ Qw) Kw
    $$ [Hi H856 Ha Sw]
  · iframe Hi H856 Ha Sw
  have hn := hm.mem
  have hg := hm.glob
  have ha923 := hm.funcs 923 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by rw [UInt32.toNat_add, h16]; simp; omega
  simp only [cost179]
  generalize hK : cost923 cfg code Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HW, HF, HP⟩
  subst hargs
  iunfold strW at HW
  icases HW with ⟨W0, W4, W8⟩
  ihave Hs := stk_addr (show sp.toNat - 16 = (sp - 16).toNat by omega) $$ Hs
  icases VecFromElem.stk16 n (sp - 16).toNat $$ Hs with ⟨S0, S4, S8, S12⟩
  iunfold stk at S8 S12
  icases S8 with ⟨%o0, %ho0, S8⟩
  icases S12 with ⟨%o4, %ho4, S12⟩
  ihave S8 := memBytes_addr (show (sp - 16).toNat + 8 = (sp - 16 + 8).toNat by omega) $$ S8
  ihave S12 := memBytes_addr (show (sp - 16).toNat + 12 = (sp - 16 + 8).toNat + 4 by omega) $$ S12
  simp only [f179]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (SerdeAccountId.f779_s cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 16 + 8) sv ptr cap len
    o0 o4 ho0 ho4) using [W0 W4 W8 S8 S12]
  · iframe W0 W4 W8 S8 S12
  icases HQ with ⟨%hrs, W0, W4, W8, S8, S12⟩
  subst hrs
  repeat mstep
  mstep [S8]
  repeat mstep
  mstep [S12]
  repeat mstep
  mcall S923 using [HF HP Hg]
  · iframe HF HP Hg
  icases HQ with ⟨%hrs, HF, Hg, HQ⟩
  subst hrs
  repeat mstep
  rw [show sp - 16 + 16 = sp by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iframe Hc Hg HF HQ
  isplitr; · ipureintro; rw [htype]; rfl
  isplitl [S0 S4 S8 S12]
  · iapply stk_addr (show (sp - 16).toNat = sp.toNat - 16 by omega)
    iapply VecFromElem.stk16_join
    iframe S0 S4
    isplitl [S8]
    · iapply stk_word
      iapply memBytes_addr (show (sp - 16 + 8).toNat = (sp - 16).toNat + 8 by omega) $$ S8
    iapply stk_word
    iapply memBytes_addr (show (sp - 16 + 8).toNat + 4 = (sp - 16).toNat + 12 by omega) $$ S12
  iunfold strW
  iframe W0 W4 W8

end Spec

end WNear.Binary.FmtStrPad
