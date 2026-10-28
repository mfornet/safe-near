import Bridge.Functions.FmtU128
import Binary.Code.Part07

/-!
# `<u128 as Display>::fmt` (901) and `<&u128 as Display>::fmt` (353)

The argument formatter `core::fmt::write` (872) calls through table entry 92 for the `u128` of
`to_string()`:

```
353 <&T as Display>::fmt(pp, f)   <u128 as Display>::fmt(*pp, f) (901)
901 <u128 as Display>::fmt(p, f)  fmt_u128(*p, *(p + 8), true, f) (902)
```

Both are specified on top of `FmtU128.f902_spec`: the `u128` at `p` as `u128Bytes lo hi`.
Costs (`regular_op_cost`s, activation excluded): 901 `23 + cost902`, 353 `14 + cost901`, plus
902's activation, the sink's activation and its cost `Kw`.
-/

namespace WNear.Binary.FmtDisplay

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtDigits
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtU128 (sinkSpec val cost pre post f902_spec ofNat_decode_i64)
open WNear.Binary.U128From (u128Bytes)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 901 runs (persistent). -/
def fmtCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (a : Nat) (code : Func) : IProp GF :=
  iprop(A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
    A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗ A 954 ↪[wf] FuncInst.wasm types[8]! inst f954 ∗
    A 900 ↪[wf] FuncInst.wasm types[56]! inst f900 ∗ A 902 ↪[wf] FuncInst.wasm types[66]! inst f902 ∗
    inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (a : Nat) (code : Func) :
    Persistent (fmtCode (GF := GF) inst mi A a code) := by
  unfold fmtCode; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<u128 as Display>::fmt(p, f)`** (901): `fmt_u128` on the `u128` at `p`. -/
theorem f901_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (lo hi : UInt64) (p s f data vtab idx : UInt32) (hp : p.toNat + 16 ≤ 2 ^ 32)
    (hs : 144 ≤ s.toNat) (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat)
    (code : Func) (Sk Sk' : IProp GF) (Kw : Nat) :
    fmtCode inst mi A a code ∗
      sinkSpec cfg lim (d + 3) inst mi n g gt (s - 144) (UInt32.ofNat (39 - (decDigits (val lo hi)).length))
        data code (decDigits (val lo hi)) Sk Sk' Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f901 Cg
        (fun args => iprop(⌜args = [.i32 p, .i32 f]⌝ ∗ n ↦[wms][ p.toNat ] u128Bytes lo hi ∗
          pre n g gt s lo hi ta f data vtab idx a Sk [.i64 lo, .i64 hi, .i32 1, .i32 f]))
        (fun _ => 23 * cfg.regularOpCost + (cost lo hi * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw))
        (fun _ rs => iprop(n ↦[wms][ p.toNat ] u128Bytes lo hi ∗
          post n g gt s ta f data vtab idx a Sk' [.i64 lo, .i64 hi, .i32 1, .i32 f] rs)) := by
  iintro ⟨#Hk, #Sw⟩
  iunfold fmtCode at Hk
  icases Hk with ⟨#H903, #H910, #H952, #H954, #H900, #H902, #Hi, #Ha⟩
  ihave #S902 := f902_spec (GF := GF) cfg lim (d + 1) types[66]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    lo hi s f data vtab idx hs hf hvt a code Sk Sk' Kw $$ [H903 H910 H952 H954 H900 Hi Ha Sw]
  · iframe H903 H910 H952 H954 H900 Hi Ha Sw
  have ha902 := hm.funcs 902 (by decide)
  have hn := hm.mem
  have t66 : types[66]!.params.length = 4 := by rfl
  generalize hK : cost lo hi * cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hp, HP⟩
  subst hargs
  rw [u128Bytes]
  icases (memBytes_append (GF := GF) (H := NearState) n p.toNat _ _).1 $$ Hp with ⟨Hp0, Hp8⟩
  simp only [U128From.storeBytes_length]
  simp only [f901]
  repeat mstep
  mstep [Hp0]
  repeat mstep
  mstep [Hp8]
  simp only [ofNat_decode_i64]
  repeat mstep
  mcall S902 using [HP]
  · iframe HP
  iunfold post at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc
  rw [htype, Nat.sub_self, List.drop_zero]
  iunfold post
  iframe HQ
  isplitl [Hp0 Hp8]
  swap
  · ipureintro; rfl
  iapply U128From.memBytes_join n p.toNat 8 _ _ (U128From.storeBytes_length _ _)
  iframe Hp0 Hp8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<&u128 as Display>::fmt(pp, f)`** (353, table entry 92): 901 on `*pp`. -/
theorem f353_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (lo hi : UInt64) (pp p s f data vtab idx : UInt32) (hpp : pp.toNat + 4 ≤ 2 ^ 32)
    (hp : p.toNat + 16 ≤ 2 ^ 32)
    (hs : 144 ≤ s.toNat) (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (a : Nat)
    (code : Func) (Sk Sk' : IProp GF) (Kw : Nat) :
    fmtCode inst mi A a code ∗ A 901 ↪[wf] FuncInst.wasm types[13]! inst f901 ∗
      sinkSpec cfg lim (d + 4) inst mi n g gt (s - 144) (UInt32.ofNat (39 - (decDigits (val lo hi)).length))
        data code (decDigits (val lo hi)) Sk Sk' Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f353 Cg
        (fun args => iprop(⌜args = [.i32 pp, .i32 f]⌝ ∗ n ↦[i32][ pp.toNat ] p ∗
          n ↦[wms][ p.toNat ] u128Bytes lo hi ∗
          pre n g gt s lo hi ta f data vtab idx a Sk [.i64 lo, .i64 hi, .i32 1, .i32 f]))
        (fun _ => 14 * cfg.regularOpCost + (23 * cfg.regularOpCost + (cost lo hi * cfg.regularOpCost +
          activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw)))
        (fun _ rs => iprop(n ↦[i32][ pp.toNat ] p ∗ n ↦[wms][ p.toNat ] u128Bytes lo hi ∗
          post n g gt s ta f data vtab idx a Sk' [.i64 lo, .i64 hi, .i32 1, .i32 f] rs)) := by
  iintro ⟨#Hk, #H901, #Sw⟩
  ihave #S901 := f901_spec (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    lo hi p s f data vtab idx hp hs hf hvt a code Sk Sk' Kw $$ [Hk Sw]
  · iframe Hk Sw
  iunfold fmtCode at Hk
  icases Hk with ⟨-, -, -, -, -, -, #Hi, -⟩
  have ha901 := hm.funcs 901 (by decide)
  have hn := hm.mem
  have t13 : types[13]!.params.length = 2 := by rfl
  generalize hK : 23 * cfg.regularOpCost + (cost lo hi * cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw) = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hpp, HP⟩
  subst hargs
  simp only [f353]
  repeat mstep
  mstep [Hpp]
  repeat mstep
  mcall S901 using [HP]
  · iframe HP
  icases HQ with ⟨Hp, HQ⟩
  iunfold post at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc Hpp Hp
  rw [htype, Nat.sub_self, List.drop_zero]
  iunfold post
  iframe HQ
  ipureintro; rfl

end Spec

end WNear.Binary.FmtDisplay
