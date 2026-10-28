import Bridge.Functions.FmtGrow
import Binary.Code.Part19
import NearLogic.Rules.CallIndirectSpec

/-!
# `Formatter::pad_integral` (903) without padding (M5)

`pad_integral(f, is_nonnegative, prefix, prefix_len, buf, len)` on the path `fmt_u128` (902)
takes for `to_string()`: `is_nonnegative`, the `Formatter`'s flags 0 (no `+`, no `#`, no
`0`) and no width (the tag word at `f + 8` is not 1). Then no sign (`1114112`, `char::MAX + 1`),
the prefix dropped (no `#`), `write_prefix` (910) writes nothing, and the digits go to the
sink in one `write_str` through the `dyn Write` vtable:

```
903  sign = 1114112; width = len; prefix = 0 (flags & 4 = 0)
     f.width is None ⇒ write_prefix(f, 1114112, 0, _) (910): Ok
                     ⇒ return (f.vtable.write_str)(f.data, buf, len)    (call_indirect, type 15)
910  sign = 1114112 ⇒ no char; prefix = 0 ⇒ Ok (0)
```

The `Formatter` at `f` is owned through `fmtr`: the flags word (0), the width tag (0), the
sink `(data, vtab)` at `f + 24`, the `write_str` slot `vtab + 12` holding the table index `idx`,
and the table entry `idx ↦ a`. `f903_spec` is parametric in the sink: any `write_str` code at
`a` with an `MFunSpec` taking `[data, buf, len]` and resources `Pw`, returning `Ok` (0) with `Qw`.
Cost: `65` `regular_op_cost`s, plus the `call_indirect`, the activation and the sink's cost.
-/

namespace WNear.Binary.FmtPad

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtGrow (mwpi_select')

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `write_prefix(f, 1114112, 0, _)` (910): no sign, no prefix, `Ok`. -/
theorem f910_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (f pl : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f910 Cg
        (fun args => iprop(⌜args = [.i32 f, .i32 1114112, .i32 0, .i32 pl]⌝))
        (fun _ => 8 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f910]
  repeat mstep
  mcredits R
  iframe Hc
  ipureintro
  match type, htype with
  | ⟨_, [_]⟩, _ => rfl

/-- The `Formatter` at `f` as `pad_integral` reads it without padding: flags 0, no width, the
sink `(data, vtab)`, its `write_str` table index `idx` and the table entry. -/
def fmtr (n ta : Nat) (f data vtab idx : UInt32) (a : Nat) : IProp GF :=
  iprop(n ↦[i32][ f.toNat ] 0 ∗ n ↦[i32][ f.toNat + 8 ] 0 ∗ n ↦[i32][ f.toNat + 24 ] data ∗
    n ↦[i32][ f.toNat + 28 ] vtab ∗ n ↦[i32][ vtab.toNat + 12 ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`pad_integral(f, true, prefix, pl, buf, len)`** (903) with flags 0 and no width: the
`len` bytes at `buf` written with the sink's `write_str` (`call_indirect`), its result returned. -/
theorem f903_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (f data vtab idx pre pl buf len : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat) (code : Func) (Pw Qw : IProp GF) (Kw : Nat) :
    A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗ inst ↪[inst] mi ∗
      a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      MFunSpec cfg lim (d + 1) types[15]! inst mi code Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 buf, .i32 len]⌝ ∗ Pw)) (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ Qw))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f903 Cg
        (fun args => iprop(⌜args = [.i32 f, .i32 1, .i32 pre, .i32 pl, .i32 buf, .i32 len]⌝ ∗
          fmtr n ta f data vtab idx a ∗ Pw))
        (fun _ => 66 * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals code [.i32 data, .i32 buf, .i32 len]) + Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtr n ta f data vtab idx a ∗ Qw)) := by
  iintro ⟨#H910, #Hi, #Ha, #Sw⟩
  have hn := hm.mem
  have hta := hm.table
  have ha910 := hm.funcs 910 (by decide)
  have t33 : types[33]!.params.length = 4 := by rfl
  have hty : types[15]! = mi.types[15]! := by rw [hm.types]
  generalize hact : activationGas cfg.regularOpCost (entryLocals code [.i32 data, .i32 buf, .i32 len]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HF, HP⟩
  subst hargs
  iunfold fmtr at HF
  icases HF with ⟨F0, F8, F24, F28, V12, Ht⟩
  have hsel : (0 : UInt32) &&& 1 = 0 := by decide
  have hand4 : Numeric.bool ((0 : UInt32) &&& 4 != 0) = 0 := by decide
  simp only [f903]
  repeat mstep
  mstep [F0]
  repeat mstep
  msel
  simp only [show UInt32.ofNat 0 &&& 1 = 0 from by decide, ite_true]
  repeat mstep
  mstep [F8]
  repeat mstep
  mcall (f910_none cfg lim (d + 1) types[33]! (by rfl) inst mi Cg f pl) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [F28]
  repeat mstep
  mstep [V12]
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 buf, Value.i32 len, Value.i32 idx] =
    [Value.i32 data, Value.i32 buf, Value.i32 len] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := cfg.regularOpCost + R) 15 0 ta idx a types[15]! inst mi code
    [.i32 data, .i32 buf, .i32 len] _ (fun _ => Kw) _ hta hty rfl (by omega)
  rw [hact]
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
  iunfold fmtr
  iframe F0 F8 F24 F28 V12 Ht

end Spec

end WNear.Binary.FmtPad
