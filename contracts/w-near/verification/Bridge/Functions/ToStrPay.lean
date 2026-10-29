import Bridge.Functions.PanicDisplay
import Bridge.Functions.PanicBegin
import Bridge.Functions.FmtWrite

/-!
# `info.to_string()` (470) on `begin_panic`'s `PanicInfo`: `PanicHook.ToStr`

```wat
;; 470 to_string(out, info)               sp -= 48
String::new() at out: (1, 0, 0)
[sp + 12] := info
Arguments { pieces: [""] (1054332), fmt: None, args: [(sp + 12, 104)] at sp + 40 } at sp + 16
r := Write::write_fmt(out, sp + 16) (746)     ;; core::fmt::write(&out, 1065404, …) (872)
Result::expect(r) (471)                   ;; Ok
sp += 48
;; 469 <&T as Display>::fmt(x, f)          <PanicInfo as Display>::fmt(*x, f) (885)
;; 471 expect(r)                          r = 0 ⇒ return
```

The `String` is `HookSink.hsink` (the empty `String` at first, `hsink_init`), the sink of 746's
`core::fmt::write` (data `sp' + 4` holding `out`, vtable 1065404, `write_str` 759 at the table entry
157). 872 writes the piece `""` and the argument through 469, i.e. `PanicDisplay.f885_pay`.

`toStr_pay`: `PanicHook.ToStr` for the `PanicInfo` at `ip` with the payload `(pp, 1062988)` (the
`&str` `(m, l)` at `pp`), no message and the location `loc`, the bytes `panicText msg file line col`;
`D` is `PanicBegin.infoD`'s shape: the `PanicInfo`, the payload's cells and `toStrEnv` (what the
formatting reads, the heap and the sink's vtable) with any frame, which the hook drops.
-/

namespace WNear.Binary.ToStrPay

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtWriteN (fmtrP Hyp872 argsN costN f872_gen)
open WNear.Binary.FmtWrite (argsAt f746_gen)
open WNear.Binary.PanicHook (ToStr stk4_word stk_split')
open WNear.Binary.PanicWithHook (infoCells)
open WNear.Binary.PanicBegin (payloadCells)
open WNear.Binary.PanicText (panicText b)
open WNear.Binary.PanicDisplay
open WNear.Binary.FmtSinkRe (sinkCodeR)
open WNear.Binary.HookSink (hsink hsink_init HsGlobal costHS)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

/-- The text after the outer 872's `i`-th write: `""`, then the `PanicInfo`. -/
def partOut (text : List UInt8) : Nat → List UInt8
  | 0 => []
  | 1 => []
  | _ => text

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`Result::expect`** (471) on `Ok` (0): returns. -/
theorem f471_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (g : Nat) (hg : mi.globalAddrs[0]? = some g)
    (Cg : Nat) (gt : GlobalType) (s : UInt32) (hs : 16 ≤ s.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f471 Cg
        (fun args => iprop(⌜args = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩))
        (fun _ => 14 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg⟩
  subst hargs
  simp only [f471]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg

/-- What the formatting reads besides the `PanicInfo` and the payload's cells: `XP` without the
payload's cells (the pieces, the vtable slot, the table entries, the message's bytes, the location). -/
def XP' (n ta : Nat) (A : Nat → Nat) (m loc file flen line col : UInt32) (msg fileB : List UInt8) :
    IProp GF :=
  iprop(n ↦[wms][ 1070672 ] pk12 ∗ (n ↦[i32][ 1062988 + 12 ] 139 ∗ ta ↦[wt][ 139 ] Ref.func (A 661)) ∗
    ((n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 ] pptrA 0 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 + 4 ] plenA 0) ∗
      (n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 ] pptrA 1 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 + 4 ] plenA 1) ∗
      ta ↦[wt][ (201 : UInt32).toNat ] Ref.func (A 886)) ∗
    ((n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 ] pptrB 0 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 + 4 ] plenB 0) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 ] pptrB 1 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 + 4 ] plenB 1) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 ] pptrB 2 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 + 4 ] plenB 2) ∗
      ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ ta ↦[wt][ (3 : UInt32).toNat ] Ref.func (A 870)) ∗
    (n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗ n ↦[wms][ m.toNat ] msg ∗
    XB n loc file flen line col fileB)

theorem XP_of (n ta : Nat) (A : Nat → Nat) (pp m l loc file flen line col : UInt32) (msg fileB : List UInt8) :
    payloadCells (GF := GF) n pp m l ∗ XP' n ta A m loc file flen line col msg fileB ⊣⊢
      XP n ta A pp m l loc file flen line col msg fileB := by
  constructor
  · iintro ⟨P, HX⟩
    iunfold payloadCells at P
    icases P with ⟨P0, P4⟩
    iunfold XP' at HX
    icases HX with ⟨Hpk, V, PA, PB, PQ, Hm, HXB⟩
    iunfold XP
    iframe Hpk V PA PB PQ Hm HXB P0 P4
  · iintro H
    iunfold XP at H
    icases H with ⟨Hpk, V, PA, PB, PQ, ⟨P0, P4, Hm⟩, HXB⟩
    iunfold payloadCells, XP'
    iframe Hpk V PA PB PQ Hm HXB P0 P4

/-- The cost of 469 on the payload path, the activation excluded. -/
noncomputable def cost469 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  8 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f885 [.i32 0, .i32 0]) +
    cost885 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<&PanicInfo as Display>::fmt(x, f)`** (469) on `*x = ip`: 885. -/
theorem f469_pay (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 7 ≤ D) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s f data vtab idx x ip pp m l loc file flen line col : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (w0 msg fileB : List UInt8)
    (hs : 304 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (hwB : w0.length + (panicText msg fileB line.toNat col.toNat).length ≤ B) :
    A 885 ↪[wf] FuncInst.wasm types[13]! inst f885 ∗ code885 inst mi A a code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f469 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ fmtrP n ta f data vtab idx a ∗
          (stk n (s.toNat - 304) 304 ∗ W w0 ∗ (n ↦[i32][ x.toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗
            XP n ta A pp m l loc file flen line col msg fileB))))
        (fun _ => cost469 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ fmtrP n ta f data vtab idx a ∗
          (stk n (s.toNat - 304) 304 ∗ W (w0 ++ panicText msg fileB line.toNat col.toNat) ∗
            (n ↦[i32][ x.toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗
              XP n ta A pp m l loc file flen line col msg fileB)))) := by
  iintro ⟨#H885, #Hk, #Sw⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code885 at Hk
    icases Hk with ⟨#Hi, -⟩
    iexact Hi
  ihave #S885 := f885_pay cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm D (by omega) (by omega) Cg gt s f data
    vtab idx ip pp m l loc file flen line col a code W B Kw w0 msg fileB hs hs2 hf hvt hip hloc hmsg hml hfl hfile
    hline hcol hwB $$ [Hk Sw]
  · iframe Hk Sw
  have hn := hm.mem
  have ha885 := hm.funcs 885 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  simp only [cost469]
  generalize hK : cost885 cfg code Kw = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, HF, Hs, HW, Hx, HI, HX⟩
  subst hargs
  simp only [f469]
  repeat mstep
  mstep [Hx]
  repeat mstep
  mcall S885 using [Hg Hs HF HI HX HW]
  · iframe Hg Hs HF HI HX HW
  icases HQ with ⟨%hrs, Hg, Hs, HF, HI, HX, HW⟩
  subst hrs
  mstep_post
  mcredits R
  iframe Hc Hg Hs HF HI HX HW Hx
  ipureintro; rw [htype]; rfl

/-- The outer 872's state: its piece `""` and its argument, below its frame `s - 48` (304 bytes of
stack for 885), the writer, and what 469 reads. -/
def StOut (n ta : Nat) (A : Nat → Nat) (s : UInt32) (W : List UInt8 → IProp GF) (text : List UInt8)
    (x ip pp m l loc file flen line col : UInt32) (msg fileB : List UInt8) (i : Nat) : IProp GF :=
  iprop(stk n ((s - 48).toNat - 304) 304 ∗ W (partOut text i) ∗
    (n ↦[i32][ x.toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗ XP n ta A pp m l loc file flen line col msg fileB))

/-- The outer 872's arrays: the piece `""` at 1054332, the argument `(x, 104)` at `argp`, the table entry. -/
def MOut (n ta : Nat) (A : Nat → Nat) (argp x : UInt32) : IProp GF :=
  iprop((n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 ] 1054332 ∗
      n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 + 4 ] 0) ∗
    (n ↦[i32][ argp.toNat + 8 * 0 ] x ∗ n ↦[i32][ argp.toNat + 8 * 0 + 4 ] 104 ∗
      ta ↦[wt][ (104 : UInt32).toNat ] Ref.func (A 469)))

/-- The code the outer 872's writes run (persistent). -/
def COut (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    IProp GF :=
  iprop(A 469 ↪[wf] FuncInst.wasm types[13]! inst f469 ∗ A 885 ↪[wf] FuncInst.wasm types[13]! inst f885 ∗
    code885 inst mi A a code ∗ SinkW cfg lim D inst mi n g gt data code W B Kw Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (COut cfg lim D inst mi A n g gt data a code W B Kw Cg) := by
  unfold COut; infer_instance

noncomputable def KB469 (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  activationGas cfg.regularOpCost (entryLocals f469 [.i32 0, .i32 0]) + cost469 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp872` for `to_string`'s `format_args!("{}", info)`**: `""`, then the `PanicInfo` (469). -/
theorem hyp_out (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 8 ≤ D) (hd : d + 9 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s data vtab idx argp x ip pp m l loc file flen line col : UInt32) (a : Nat)
    (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (msg fileB : List UInt8)
    (hs : 352 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (hwB : (panicText msg fileB line.toNat col.toNat).length ≤ B) :
    Hyp872 (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1054332 argp 1 (fun _ => 1054332)
      (fun _ => 0) (fun _ => x) (fun _ => 104) (fun _ => A 469) (fun _ => f469) a code
      (COut cfg lim D inst mi A n g gt data a code W B Kw Cg) (MOut n ta A argp x)
      (StOut n ta A s W (panicText msg fileB line.toNat col.toNat) x ip pp m l loc file flen line col msg fileB)
      Kw (cost469 cfg code Kw) (KB469 cfg code Kw) := by
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
    iunfold MOut at H
    icases H with ⟨⟨P0, P4⟩, Q⟩
    iframe P0 P4
    iintro ⟨P0, P4⟩
    iunfold MOut
    iframe P0 P4 Q
  · intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MOut at H
    icases H with ⟨P, ⟨Q0, Q4, Qt⟩⟩
    iframe Q0 Q4 Qt
    iintro ⟨Q0, Q4, Qt⟩
    iunfold MOut
    iframe P Q0 Q4 Qt
  · iintro #C
    iunfold COut, code885 at C
    icases C with ⟨-, -, ⟨#Hi, -, -, -, -, -, -, -, -, -, #Ha⟩, -⟩
    iframe Hi Ha
  · intro j hj
    rcases hj1 j hj
    simp only [StOut, Nat.reduceMul]
    iintro #C
    iunfold COut at C
    icases C with ⟨-, -, -, #Sw⟩
    iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1054332 0 304
      (partOut (panicText msg fileB line.toNat col.toNat) 0) (partOut (panicText msg fileB line.toNat col.toNat) 1)
      [] _ (by omega) (by omega) (by omega) rfl (by decide) (by simp [partOut]) (by simp [partOut])
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
    iunfold COut at C
    icases C with ⟨#H469, -⟩
    iexact H469
  · intro j hj
    rcases hj1 j hj
    simp only [StOut, Nat.reduceMul, Nat.reduceAdd]
    iintro #C
    iunfold COut at C
    icases C with ⟨-, #H885, #Hk, #Sw⟩
    ihave #S := f469_pay cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48)
      (s - 48 + 8) data vtab idx x ip pp m l loc file flen line col a code W B Kw [] msg fileB (by omega) (by omega)
      (by omega) hvt hip hloc hmsg hml hfl hfile hline hcol (by simpa using hwB) $$ [H885 Hk Sw]
    · iframe H885 Hk Sw
    simp only [partOut, List.nil_append]
    iexact S
  · intro j hj
    rcases hj1 j hj
    unfold KB469; omega

/-! ## `to_string` (470) -/

/-- What `to_string` reads and uses besides the `PanicInfo` and the payload's cells: `XP'`, the
allocator's vtable slot and the heap, the sink's vtable slot (1065404, `write_str` at 157) and the
table entries 157 (759) and 104 (469), the piece `""` of `format_args!("{}", info)` at 1054332. -/
def toStrEnv (n ta : Nat) (A : Nat → Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (idx : UInt32)
    (m loc file flen line col : UInt32) (msg fileB : List UInt8) : IProp GF :=
  iprop(XP' n ta A m loc file flen line col msg fileB ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
    (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
      ta ↦[wt][ (104 : UInt32).toNat ] Ref.func (A 469)) ∗
    (n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 ] 1054332 ∗ n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 + 4 ] 0))

/-- The code `to_string` runs (persistent). -/
def codeTS (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(sinkCodeR n maxP inst mi A ∗ code885 inst mi A (A 759) f759 ∗
    A 759 ↪[wf] FuncInst.wasm types[15]! inst f759 ∗
    A 469 ↪[wf] FuncInst.wasm types[13]! inst f469 ∗ A 885 ↪[wf] FuncInst.wasm types[13]! inst f885 ∗
    A 746 ↪[wf] FuncInst.wasm types[13]! inst f746 ∗ A 471 ↪[wf] FuncInst.wasm types[0]! inst f471)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (codeTS (GF := GF) n maxP inst mi A) := by
  unfold codeTS; infer_instance

/-- 470's frame back from its words. -/
theorem frame48 (n a : Nat) (junk : List UInt8) (hj : junk.length = 4)
    (w12 w16 w20 w24 w32 w36 w40 w44 : UInt32) :
    stk (GF := GF) n a 12 ∗ n ↦[i32][ a + 12 ] w12 ∗ n ↦[i32][ a + 16 ] w16 ∗ n ↦[i32][ a + 20 ] w20 ∗
      n ↦[i32][ a + 24 ] w24 ∗ n ↦[wms][ a + 28 ] junk ∗ n ↦[i32][ a + 32 ] w32 ∗ n ↦[i32][ a + 36 ] w36 ∗
      n ↦[i32][ a + 40 ] w40 ∗ n ↦[i32][ a + 44 ] w44 ⊢ stk n a 48 := by
  iintro ⟨X0, W12, W16, W20, W24, W28, W32, W36, W40, W44⟩
  ihave W12 := stk_word n _ _ $$ W12
  ihave W16 := stk_word n _ _ $$ W16
  ihave W20 := stk_word n _ _ $$ W20
  ihave W24 := stk_word n _ _ $$ W24
  ihave W28 := FmtU128.stk_of n _ 4 _ hj $$ W28
  ihave W32 := stk_word n _ _ $$ W32
  ihave W36 := stk_word n _ _ $$ W36
  ihave W40 := stk_word n _ _ $$ W40
  ihave W44 := stk_word n _ _ $$ W44
  ihave H := stkJ (a := a + 40) (b := a + 44) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [W40 W44]
  · iframe W40 W44
  ihave H := stkJ (a := a + 36) (b := a + 40) (k1 := 4) (k2 := 8) (k := 12) (by omega) rfl $$ [W36 H]
  · iframe W36 H
  ihave H := stkJ (a := a + 32) (b := a + 36) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [W32 H]
  · iframe W32 H
  ihave H := stkJ (a := a + 28) (b := a + 32) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [W28 H]
  · iframe W28 H
  ihave H := stkJ (a := a + 24) (b := a + 28) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [W24 H]
  · iframe W24 H
  ihave H := stkJ (a := a + 20) (b := a + 24) (k1 := 4) (k2 := 24) (k := 28) (by omega) rfl $$ [W20 H]
  · iframe W20 H
  ihave H := stkJ (a := a + 16) (b := a + 20) (k1 := 4) (k2 := 28) (k := 32) (by omega) rfl $$ [W16 H]
  · iframe W16 H
  ihave H := stkJ (a := a + 12) (b := a + 16) (k1 := 4) (k2 := 32) (k := 36) (by omega) rfl $$ [W12 H]
  · iframe W12 H
  iapply stkJ (a := a) (b := a + 12) (k1 := 12) (k2 := 36) (k := 48) rfl rfl
  iframe X0 H

/-- `to_string`'s cost on `begin_panic`'s `PanicInfo`. -/
noncomputable def costTS (cfg : WasmConfig) (F J B : Nat) : Nat :=
  200 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f746 [.i32 0, .i32 0]) +
    activationGas cfg.regularOpCost (entryLocals f471 [.i32 0]) +
    activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
    costN cfg f759 (costHS cfg F J B B) (KB469 cfg f759 (costHS cfg F J B B)) 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`info.to_string()` (470) on `begin_panic`'s `PanicInfo`**: `PanicHook.ToStr` with the bytes
`panicText msg file line col`. -/
theorem toStr_pay (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 27 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s ip pp m l loc file flen line col idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsS : S ≤ s.toNat)
    (hs2 : s.toNat + 28 ≤ 2 ^ 32)
    (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (msg fileB : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J : Nat)
    (HG : HsGlobal maxP L0 F J (panicText msg fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (Fr : IProp GF) :
    codeTS n maxP inst mi A ⊢
      ToStr (GF := GF) cfg lim d inst mi Cg n g gt s ip S
        iprop(infoCells n ip pp 1062988 0 loc ∗ payloadCells n pp m l ∗
          (toStrEnv n ta A maxP hl live F idx m loc file flen line col msg fileB ∗ Fr))
        (costTS cfg F J (panicText msg fileB line.toNat col.toNat).length)
        (panicText msg fileB line.toNat col.toNat) := by
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h80 : (s - 48 - 32).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h16o : (s + 16).toNat = s.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have hdd : (s - 48 - 32 + 4).toNat = s.toNat - 76 := by simp [UInt32.toNat_add, h80]; omega
  have h128 : (s - 48 - 32 - 48).toNat = s.toNat - 128 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have hx : (s - 48 + 12).toNat = s.toNat - 36 := by simp [UInt32.toNat_add, h48]; omega
  have hap : (s - 48 + 16).toNat = s.toNat - 32 := by simp [UInt32.toNat_add, h48]; omega
  have hargp : (s - 48 + 40).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h48]; omega
  have hlim : 17 ≤ lim.maxCallDepth := by omega
  iintro #Hc0
  ihave #Hc1 := Hc0
  iunfold codeTS at Hc1
  icases Hc1 with ⟨#Hsk, #Hk885, #H759, #H469, #H885, #H746, #H471⟩
  ihave #Hk' := Hk885
  iunfold code885 at Hk'
  icases Hk' with ⟨#Hi, #H872, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha746 := hm.funcs 746 (by decide)
  have ha471 := hm.funcs 471 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  ihave #Sw := hsink_sinkW (GF := GF) cfg lim inst mi A n g ta hm Cg gt maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx
    (s - 48 - 32 + 4) HG (by omega) (by omega) hlim $$ Hsk
  ihave #Co : COut cfg lim (lim.maxCallDepth - 17) inst mi A n g gt (s - 48 - 32 + 4) (A 759) f759
      (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
      (panicText msg fileB line.toNat col.toNat).length (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length (panicText msg fileB line.toNat col.toNat).length) Cg $$ [H469 H885 Hk885 Sw]
  · iunfold COut; iframe H469 H885 Hk885 Sw
  -- the outer 872 in the shape `f746_gen` asks
  have S872 := f872_gen (GF := GF) cfg lim (d + 1 + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 48 - 32) (s - 48 - 32 + 4) 1065404 (s - 48 - 32 + 8) 1054332 (s - 48 + 40) 157 1 (by decide) (by omega)
    (by simp [UInt32.toNat_add, h80]; omega) (by simp) (by simp; omega)
    (fun _ => 1054332) (fun _ => 0) (fun _ => s - 48 + 12) (fun _ => 104) (fun _ => A 469) (fun _ => f469) (A 759) f759
    (COut cfg lim (lim.maxCallDepth - 17) inst mi A n g gt (s - 48 - 32 + 4) (A 759) f759
      (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
      (panicText msg fileB line.toNat col.toNat).length
      (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length
        (panicText msg fileB line.toNat col.toNat).length) Cg)
    (MOut n ta A (s - 48 + 40) (s - 48 + 12))
    (StOut n ta A (s - 48 - 32)
      (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
      (panicText msg fileB line.toNat col.toNat) (s - 48 + 12) ip pp m l loc file flen line col msg fileB)
    (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length
      (panicText msg fileB line.toNat col.toNat).length)
    (cost469 cfg f759 (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length
      (panicText msg fileB line.toNat col.toNat).length))
    (KB469 cfg f759 (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length
      (panicText msg fileB line.toNat col.toNat).length))
    (hyp_out cfg lim (d + 1 + 1) inst mi A n g ta hm (lim.maxCallDepth - 17) (by omega) (by omega) Cg gt
      (s - 48 - 32) (s - 48 - 32 + 4) 1065404 157 (s - 48 + 40) (s - 48 + 12) ip pp m l loc file flen line col
      (A 759) f759 _ _ _ msg fileB (by omega) (by omega) (by decide) hip hloc hmsg hml hfl hfile hline hcol le_rfl)
  rw [show 2 * (1 : UInt32).toNat = 2 from rfl] at S872
  have S872' := S872.trans (MFunSpec_frame (GF := GF) (Fr := iprop(emp))
    (P' := fun args => iprop(⌜args = [.i32 (s - 48 - 32 + 4), .i32 1065404, .i32 (s - 48 - 32 + 8)]⌝ ∗
      g ↦[wg] ⟨gt, .i32 (s - 48 - 32)⟩ ∗ argsAt n (s - 48 - 32 + 8) 1054332 (s - 48 + 40) ∗
      n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
      (stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) [] ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗
          XP n ta A pp m l loc file flen line col msg fileB))))
    (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48 - 32)⟩ ∗
      argsAt n (s - 48 - 32 + 8) 1054332 (s - 48 + 40) ∗ n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
      (stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578)
          (panicText msg fileB line.toNat col.toNat) ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗
          XP n ta A pp m l loc file flen line col msg fileB))))
    (fun args => by
      iintro ⟨%ha, Hg, HA, Hd, Hs, HM, ⟨V157, T157⟩, HS, HX⟩
      icases stkSp 304 48 rfl $$ Hs with ⟨Hs1, Hs2⟩
      isplitl
      · iframe Hg HM V157 T157
        isplitr; · ipureintro; exact ha
        isplitl [Hs2]; · iapply stkA (by omega) $$ Hs2
        isplitl [HA]; · iunfold argsAt at HA; iunfold argsN; iexact HA
        iunfold StOut
        isplitl [Hs1]; · iapply stkA (by omega) $$ Hs1
        simp only [partOut]
        iframe Hd HS HX
      · iempintro)
    (fun args rs => by
      iintro ⟨-, %hrs, Hg, Hs2, HA, HM, V157, T157, HSt⟩
      iunfold StOut at HSt
      icases HSt with ⟨Hs1, ⟨Hd, HS⟩, HX⟩
      iframe Hg HM V157 T157 HX Hd
      isplitr; · ipureintro; exact hrs
      isplitl [HA]; · iunfold argsN at HA; iunfold argsAt; iexact HA
      simp only [partOut]
      iframe HS
      iapply stkJ (a := (s - 48 - 32).toNat - 352) (b := (s - 48 - 32).toNat - 48) (k1 := 304) (k2 := 48)
        (by omega) rfl
      isplitl [Hs1]; · iapply stkA (by omega) $$ Hs1
      iexact Hs2))
  ihave #S872'' := S872' $$ Co
  unfold ToStr
  simp only [costTS]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hout, HI, HPc, HE, -⟩
  subst hargs
  iunfold toStrEnv at HE
  icases HE with ⟨HX', Hvt, Hh, ⟨V157, T157, T104⟩, ⟨P0, P4⟩⟩
  ihave HXP := (XP_of n ta A pp m l loc file flen line col msg fileB).1 $$ [HPc HX']
  · iframe HPc HX'
  -- the stack: S - 432 unused, 352 for 872 and below, 746's 32, 470's 48
  icases stk_split' n _ S (S - 432) 432 (by omega) $$ Hs with ⟨Hlo, Hs⟩
  icases stk_split' n _ 432 352 80 rfl $$ Hs with ⟨H352, Hs⟩
  icases stk_split' n _ 80 32 48 rfl $$ Hs with ⟨H746, Fr⟩
  icases stk_split' n _ 48 12 36 rfl $$ Fr with ⟨X0, Fr⟩
  icases stk_split' n _ 36 4 32 rfl $$ Fr with ⟨W12, Fr⟩
  icases stk_split' n _ 32 4 28 rfl $$ Fr with ⟨W16, Fr⟩
  icases stk_split' n _ 28 8 20 rfl $$ Fr with ⟨W20, Fr⟩
  icases stk_split' n _ 20 4 16 rfl $$ Fr with ⟨W28, Fr⟩
  icases stk_split' n _ 16 4 12 rfl $$ Fr with ⟨W32, Fr⟩
  icases stk_split' n _ 12 4 8 rfl $$ Fr with ⟨W36, Fr⟩
  icases stk_split' n _ 8 4 4 rfl $$ Fr with ⟨W40, W44⟩
  icases stk4_word n _ $$ W12 with ⟨%o12, W12⟩
  icases stk4_word n _ $$ W16 with ⟨%o16, W16⟩
  icases stk4_word n _ $$ W32 with ⟨%o32, W32⟩
  icases stk4_word n _ $$ W36 with ⟨%o36, W36⟩
  icases stk4_word n _ $$ W40 with ⟨%o40, W40⟩
  icases stk4_word n _ $$ W44 with ⟨%o44, W44⟩
  iunfold stk at W20 W28
  icases W20 with ⟨%o20, %ho20, W20⟩
  icases W28 with ⟨%junk, %hjunk, W28⟩
  icases stk_split' n _ 12 8 4 rfl $$ Hout with ⟨O0, O8⟩
  icases stk4_word n _ $$ O8 with ⟨%q8, O8⟩
  iunfold stk at O0
  icases O0 with ⟨%q0, %hq0, O0⟩
  ihave #S746 := f746_gen cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 48) (s + 16)
    (s - 48 + 16) 1054332 (s - 48 + 40) junk hjunk (by omega) (by omega)
    iprop(stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) [] ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗
          XP n ta A pp m l loc file flen line col msg fileB))
    iprop(stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta (A 578)
          (panicText msg fileB line.toNat col.toNat) ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp 1062988 0 loc ∗
          XP n ta A pp m l loc file flen line col msg fileB))
    _ $$ [Hi H872 S872'']
  · iframe Hi H872 S872''
  simp only [f470]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [O8]
  repeat mstep
  mstep [O0]
  repeat mstep
  mstep [W12]
  repeat mstep
  mstep [W36]
  repeat mstep
  mstep [W20]
  repeat mstep
  mstep [W16]
  repeat mstep
  mstep [W44]
  repeat mstep
  mstep [W32]
  repeat mstep
  mstep [W40]
  repeat mstep
  rw [show storeBytes (.i64 1) 8 = bytes32 1 ++ bytes32 0 by decide]
  icases (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 1) (bytes32 0)).1 $$ O0 with ⟨O0, O4⟩
  icases (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 1) (bytes32 0)).1 $$ W20 with ⟨W20, W24⟩
  ihave HS := hsink_init n maxP L0 live F J (panicText msg fileB line.toNat col.toNat).length (s + 16) idx ta
    (A 578) hl hl0 hl1 hlL $$ [Hvt O0 O4 O8 Hh]
  · iframe Hvt Hh
    isplitl [O0]; · iapply memBytes_addr _ $$ O0; omega
    isplitl [O4]; · iapply memBytes_addr _ $$ O4; simp [bytes32]; omega
    iapply memBytes_addr _ $$ O8; omega
  mcall S746 using [Hg H746 W16 W20 W24 W28 W32 W36 H352 P0 P4 W40 W44 T104 V157 T157 HS W12 HI HXP]
  · iframe Hg V157 T157 HS HI HXP
    isplitl [H746]; · iapply stk_addr _ $$ H746; omega
    isplitl [W16 W20 W24 W32 W36]
    · iunfold argsAt
      isplitl [W16]; · iapply memBytes_addr _ $$ W16; omega
      isplitl [W20]; · iapply memBytes_addr _ $$ W20; omega
      isplitl [W24]; · iapply memBytes_addr _ $$ W24; simp [bytes32]; omega
      isplitl [W32]; · iapply memBytes_addr _ $$ W32; omega
      iapply memBytes_addr _ $$ W36; omega
    isplitl [W28]; · iapply memBytes_addr _ $$ W28; omega
    isplitl [H352]; · iapply stk_addr _ $$ H352; omega
    isplitl [P0 P4 W40 W44 T104]
    · iunfold MOut
      simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.add_zero, Nat.reduceAdd]
      iframe P0 P4 T104
      isplitl [W40]; · iapply memBytes_addr _ $$ W40; omega
      iapply memBytes_addr _ $$ W44; omega
    iapply memBytes_addr _ $$ W12; omega
  icases HQ with ⟨%hrs, Hg, H746, HA, HJ, H352, HM, ⟨V157, T157⟩, HS, W12, HI, HXP⟩
  subst hrs
  mcall (f471_ok cfg lim (d + 1) types[0]! rfl inst mi g hg Cg gt (s - 48) (by omega)) using [Hg]
  · iframe Hg
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 48 + 48 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg
  iunfold hsink at HS
  icases HS with ⟨-, %ptr, %cap, %hl', %F', %rest, %⟨hok, hwr⟩, V0, V4, V8, Hb, -⟩
  iunfold argsAt at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  iunfold MOut at HM
  icases HM with ⟨-, M0, M4, -⟩
  isplitl [Hlo H352 H746 X0 W12 A0 A4 A8 HJ A16 A20 M0 M4]
  · ihave Fr := frame48 n (s - 48).toNat junk hjunk _ _ _ _ _ _ _ _ $$ [X0 W12 A0 A4 A8 HJ A16 A20 M0 M4]
    · isplitl [X0]; · iapply stk_addr _ $$ X0; omega
      isplitl [W12]; · iapply memBytes_addr _ $$ W12; omega
      isplitl [A0]; · iapply memBytes_addr _ $$ A0; omega
      isplitl [A4]; · iapply memBytes_addr _ $$ A4; omega
      isplitl [A8]; · iapply memBytes_addr _ $$ A8; omega
      isplitl [HJ]; · iapply memBytes_addr _ $$ HJ; omega
      isplitl [A16]; · iapply memBytes_addr _ $$ A16; omega
      isplitl [A20]; · iapply memBytes_addr _ $$ A20; omega
      isplitl [M0]; · iapply memBytes_addr _ $$ M0; omega
      iapply memBytes_addr _ $$ M4; omega
    ihave H := stkJ (a := (s - 48 - 32).toNat - 352) (b := (s - 48).toNat - 32) (k1 := 352) (k2 := 32) (k := 384)
      (by omega) rfl $$ [H352 H746]
    · iframe H352 H746
    ihave H := stkJ (a := (s - 48 - 32).toNat - 352) (b := (s - 48).toNat) (k1 := 384) (k2 := 48) (k := 432)
      (by omega) rfl $$ [H Fr]
    · iframe H Fr
    iapply stkJ (a := s.toNat - S) (b := (s - 48 - 32).toNat - 352) (k1 := S - 432) (k2 := 432) (k := S)
      (by omega) (by omega)
    iframe Hlo H
  iexists ptr, cap
  icases splitB (a := ptr.toNat) (b := ptr.toNat + (panicText msg fileB line.toNat col.toNat).length)
    (panicText msg fileB line.toNat col.toNat) rest rfl $$ Hb with ⟨Hb, -⟩
  iframe Hb
  isplitl [V0]; · iapply memBytes_addr _ $$ V0; omega
  isplitl [V4]; · iapply memBytes_addr _ $$ V4; omega
  iapply memBytes_addr _ $$ V8; omega

end Spec

end WNear.Binary.ToStrPay
