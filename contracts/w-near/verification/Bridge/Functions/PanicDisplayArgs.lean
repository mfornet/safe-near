import Bridge.Functions.HookSink
import Bridge.Functions.FmtStrPad
import Bridge.Functions.FmtU64
import Bridge.Functions.FmtWriteT
import Binary.Code.Part09

/-!
# The writer of `<PanicInfo as Display>` and the arguments it formats

`<PanicInfo as Display>::fmt` (885) writes through its `Formatter`'s sink. `SinkW` abstracts that
sink: a writer state `W w` (the bytes `w` written so far) and a `write_str` (code `code`, data
`data`) that appends any `k` bytes while `|w| + k ≤ B`, at a cost `Kw`, from any stack pointer with
112 bytes below it and any call depth up to `D`. `hsink_sinkW`: `HookSink.hsink` is one.

On `SinkW`, the formatters 885 calls:

* `f856_w`: `Formatter::pad` (856) without width or precision (`FmtStrPad.f856_plain`);
* `f880_w`: `<&str as Display>::fmt` (880, table entry 195) on `x` holding the `&str` `(p, k)`;
* `f886_w`: `<&&str as Display>::fmt` (886, table entry 201) on `y` holding the address of the
  `&str`: the payload's `&str` of `begin_panic`;
* `sinkW_64`: the sink as `fmt_u64`'s (`FmtU64.sinkSpec64`), for `<u32 as Display>` (870, table
  entry 3).

```wat
;; 880 (x, f)   pad(f, [x], [x + 4])
;; 886 (y, f)   pad(f, [[y]], [[y] + 4])
```
-/

namespace WNear.Binary.PanicDisplay

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtWriteN (fmtrP)
open WNear.Binary.FmtStrPad (f856_plain cost856)
open WNear.Binary.FmtSinkRe (sinkCodeR)
open WNear.Binary.HookSink (hsink hsink_w costHS HsGlobal)
open WNear.Binary.FmtU64 (sinkSpec64)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **A sink**: `write_str` (the code `code` on the data `data`) appends `k` bytes to the writer
state `W w` while `|w| + k ≤ B`, at the cost `Kw`, at any depth `d ≤ D`, from any stack pointer with
112 bytes of stack below it. -/
def SinkW (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) : IProp GF :=
  iprop(□ ∀ d : Nat, ∀ s : UInt32, ∀ p : UInt32, ∀ k : UInt32, ∀ w : List UInt8, ∀ sb : List UInt8,
    ⌜d ≤ D ∧ 112 ≤ s.toNat ∧ sb.length = k.toNat ∧ p.toNat + k.toNat ≤ 2 ^ 32 ∧ w.length + k.toNat ≤ B⌝ -∗
    MFunSpec cfg lim d types[15]! inst mi code Cg
      (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))
      (fun _ => Kw)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)))

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (SinkW cfg lim D inst mi n g gt data code W B Kw Cg) := by
  unfold SinkW; infer_instance

/-- **`to_string`'s `String` is a sink**: `*dd = v` and `hsink` at `v`, through 759. -/
theorem hsink_sinkW (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType) (maxP L0 : Nat)
    (live : List (Nat × Nat)) (F J B : Nat) (v idx dd : UInt32) (HG : HsGlobal maxP L0 F J B)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hlim : 17 ≤ lim.maxCallDepth) :
    sinkCodeR n maxP inst mi A ⊢
      SinkW (GF := GF) cfg lim (lim.maxCallDepth - 17) inst mi n g gt dd f759
        (fun w => iprop(n ↦[i32][ dd.toNat ] v ∗ hsink n maxP L0 live F J B v idx ta (A 578) w)) B
        (costHS cfg F J B B) Cg := by
  iintro #Hk
  iunfold SinkW
  imodintro
  iintro %d %s %p %k %w %sb %⟨hdD, hs, hsb, hp, hwB⟩
  dsimp only
  have S := hsink_w (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm (by omega) Cg gt maxP L0 live
    F J B v idx HG hv s dd p k w sb hs hdd hsb hp hwB
  have S' := S.trans ((MFunSpec_frame (Fr := iprop(emp))
    (P' := fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ hsink n maxP L0 live F J B v idx ta (A 578) w) ∗
      n ↦[wms][ p.toNat ] sb))
    (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ hsink n maxP L0 live F J B v idx ta (A 578) (w ++ sb)) ∗
      n ↦[wms][ p.toNat ] sb)) ?_ ?_).trans (MFunSpec_cost (K' := fun _ => costHS cfg F J B B) ?_))
  · iapply S' $$ Hk
  · intro args
    iintro ⟨%ha, Hg, Hs, ⟨Hd, HS⟩, Hp⟩
    isplitl
    · iframe Hg Hs Hd HS Hp; ipureintro; exact ha
    · iempintro
  · intro args rs
    iintro ⟨-, %hrs, Hg, Hs, Hd, HS, Hp⟩
    iframe Hg Hs Hd HS Hp; ipureintro; exact hrs
  · intro _
    have hmc : MemCpy.cost k.toNat ≤ MemCpy.cost B := by
      unfold MemCpy.cost; split <;> split <;> omega
    have := Nat.mul_le_mul_right cfg.regularOpCost hmc
    simp only [costHS]; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`Formatter::pad(f, p, k)`** (856) on the sink `SinkW`: the `k` bytes at `p` appended. -/
theorem f856_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 1 ≤ D) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp f data vtab idx p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (hsp : 112 ≤ sp.toNat)
    (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (w sb : List UInt8)
    (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) :
    inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f856 Cg
        (fun args => iprop(⌜args = [.i32 f, .i32 p, .i32 k]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb)))
        (fun _ => cost856 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb))) := by
  iintro ⟨#Hi, #Ha, #Sw⟩
  iunfold SinkW at Sw
  ihave #S := Sw $$ %(d + 1) %sp %p %k %w %sb %⟨hdD, hsp, hsb, hp, hwB⟩
  iapply f856_plain cfg lim d type htype inst mi A n g ta hm hd Cg f data vtab idx p k hf a code
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb)
    iprop(g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb) Kw
  iframe Hi Ha S

/-- The cost of 880 and 886 on `SinkW`, the activation excluded. -/
noncomputable def cost880 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  12 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f856 [.i32 0, .i32 0, .i32 0]) +
    cost856 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`<&str as Display>::fmt(x, f)`** (880) on `*x = (p, k)`: `pad(f, p, k)`. -/
theorem f880_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 2 ≤ D) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp f data vtab idx x p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (hsp : 112 ≤ sp.toNat)
    (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (w sb : List UInt8)
    (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f880 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (n ↦[i32][ x.toNat ] p ∗ n ↦[i32][ x.toNat + 4 ] k ∗
            (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))))
        (fun _ => cost880 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (n ↦[i32][ x.toNat ] p ∗ n ↦[i32][ x.toNat + 4 ] k ∗
            (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)))) := by
  iintro ⟨#Hi, #H856, #Ha, #Sw⟩
  ihave #S856 := f856_w cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm D (by omega) (by omega) Cg gt sp f
    data vtab idx p k hf hsp a code W B Kw w sb hsb hp hwB $$ [Hi Ha Sw]
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
set_option maxHeartbeats 4000000 in
/-- **`<&&str as Display>::fmt(y, f)`** (886) on `*y = pp`, `*pp = (p, k)`: `pad(f, p, k)`. -/
theorem f886_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 2 ≤ D) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp f data vtab idx y pp p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (hsp : 112 ≤ sp.toNat)
    (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (w sb : List UInt8)
    (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ B) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f886 Cg
        (fun args => iprop(⌜args = [.i32 y, .i32 f]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (n ↦[i32][ y.toNat ] pp ∗ n ↦[i32][ pp.toNat ] p ∗ n ↦[i32][ pp.toNat + 4 ] k ∗
            (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))))
        (fun _ => cost880 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ fmtrP n ta f data vtab idx a ∗
          (n ↦[i32][ y.toNat ] pp ∗ n ↦[i32][ pp.toNat ] p ∗ n ↦[i32][ pp.toNat + 4 ] k ∗
            (g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)))) := by
  iintro ⟨#Hi, #H856, #Ha, #Sw⟩
  ihave #S856 := f856_w cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm D (by omega) (by omega) Cg gt sp f
    data vtab idx p k hf hsp a code W B Kw w sb hsb hp hwB $$ [Hi Ha Sw]
  · iframe Hi Ha Sw
  have hn := hm.mem
  have ha856 := hm.funcs 856 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  simp only [cost880]
  generalize hK : cost856 cfg code Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HF, Y0, P0, P4, HP⟩
  subst hargs
  simp only [f886]
  repeat mstep
  mstep [Y0]
  repeat mstep
  mstep [P0]
  repeat mstep
  mstep [P4]
  repeat mstep
  mcall S856 using [HF HP]
  · iframe HF HP
  icases HQ with ⟨%hrs, HF, HP⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc HF Y0 P0 P4 HP
  ipureintro; rw [htype]; rfl

/-- **The sink as `fmt_u64`'s**: at `sp` with 112 bytes below it, the writer `W w` and the stack as
`Sk`. -/
theorem sinkW_64 (cfg : WasmConfig) (lim : ExecLimits) (D d inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (sp data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat)
    (w ds : List UInt8) (hdD : d ≤ D) (hsp : 112 ≤ sp.toNat) (hsp2 : sp.toNat + 48 ≤ 2 ^ 32)
    (hds : ds.length ≤ 39) (hwB : w.length + ds.length ≤ B) :
    SinkW cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      sinkSpec64 (GF := GF) cfg lim d inst mi n g gt sp data code ds
        iprop(stk n (sp.toNat - 112) 112 ∗ W w) iprop(stk n (sp.toNat - 112) 112 ∗ W (w ++ ds)) Kw Cg := by
  iintro #Sw
  iunfold SinkW at Sw
  iunfold sinkSpec64
  imodintro
  iintro %p %k %⟨hp, hk⟩
  ihave #S := Sw $$ %d %sp %p %k %w %ds %⟨hdD, hsp, hk.symm, by omega, by omega⟩
  iapply (MFunSpec_frame (GF := GF) (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] ds))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 112) 112 ∗ W (w ++ ds) ∗ n ↦[wms][ p.toNat ] ds))
    (fun args => by
      iintro ⟨%ha, Hg, Hp, Hs, HW⟩
      isplitl
      · iframe Hg Hp Hs HW; ipureintro; exact ha
      · iempintro)
    (fun args rs => by
      iintro ⟨-, %hrs, Hg, Hs, HW, Hp⟩
      iframe Hg Hp Hs HW; ipureintro; exact hrs))
  iexact S

end Spec

end WNear.Binary.PanicDisplay
