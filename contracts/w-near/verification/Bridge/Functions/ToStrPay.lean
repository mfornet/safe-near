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

end Spec

end WNear.Binary.ToStrPay
