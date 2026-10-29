import Bridge.Functions.ToStrPay
import Bridge.Functions.PanicDisplayMsg
import Bridge.Functions.PanicMsgArgs

/-!
# `info.to_string()` (470) on a `PanicInfo` with a message: `PanicHook.ToStr`

`ToStrPay` on the message path: 470 → 746 → 872 (`format_args!("{}", info)`) → 469 → 885 on the
`PanicInfo` at `ip` with the message `a0` (`PanicDisplayMsg.f885_msg`), on `to_string`'s `String`
(`HookSink.hsink`, through 759).

`toStr_msg`: `PanicHook.ToStr` with the bytes `panicText text file line col`, `text` what the
message's `Arguments` format to: a premise `hMsg` gives `PanicMsg.MsgW` on any sink of
`to_string`'s shape (`PanicMsg.msgW_expect`, `PanicMsg.msgW_str`).
-/

namespace WNear.Binary.ToStrMsg

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
open WNear.Binary.PanicText (panicText b)
open WNear.Binary.PanicDisplay
open WNear.Binary.PanicDisplayMsg
open WNear.Binary.PanicMsg (MsgW)
open WNear.Binary.FmtSinkRe (sinkCodeR)
open WNear.Binary.HookSink (hsink hsink_init HsGlobal costHS)
open WNear.Binary.ToStrPay (partOut f471_ok MOut frame48)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of 469 on the message path, the activation excluded. -/
noncomputable def cost469M (cfg : WasmConfig) (code : Func) (Kw Km : Nat) : Nat :=
  8 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f885 [.i32 0, .i32 0]) +
    cost885M cfg code Kw Km

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<&PanicInfo as Display>::fmt(x, f)`** (469) on `*x = ip`, a `PanicInfo` with a message: 885. -/
theorem f469_msg (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D DM : Nat) (hdD : d + 7 ≤ D) (hdM : d + 4 ≤ DM) (hd : d + 8 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType)
    (s f data vtab idx x ip pp0 pv a0 pp argp kp k loc file flen line col : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (Xm : IProp GF) (Km : Nat) (w0 text fileB : List UInt8)
    (hs : 304 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (ha0 : a0 ≠ 0) (ha0b : a0.toNat + 24 ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (hwB : w0.length + (panicText text fileB line.toNat col.toNat).length ≤ B) :
    A 885 ↪[wf] FuncInst.wasm types[13]! inst f885 ∗ code885M inst mi A a code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg ∗
      MsgW cfg lim DM inst mi n g ta gt data vtab idx a W B pp argp kp k (XmT ta A Xm) text Km Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f469 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ fmtrP n ta f data vtab idx a ∗
          (stk n (s.toNat - 304) 304 ∗ W w0 ∗ (n ↦[i32][ x.toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
            XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB))))
        (fun _ => cost469M cfg code Kw Km)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ fmtrP n ta f data vtab idx a ∗
          (stk n (s.toNat - 304) 304 ∗ W (w0 ++ panicText text fileB line.toNat col.toNat) ∗
            (n ↦[i32][ x.toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
              XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB)))) := by
  iintro ⟨#H885, #Hk, #Sw, #Mw⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code885M at Hk
    icases Hk with ⟨#Hi, -⟩
    iexact Hi
  ihave #S885 := f885_msg cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm D DM (by omega) (by omega)
    (by omega) Cg gt s f data vtab idx ip pp0 pv a0 pp argp kp k loc file flen line col a code W B Kw Xm Km
    w0 text fileB hs hs2 hf hvt hip hloc ha0 ha0b hfl hfile hline hcol hwB $$ [Hk Sw Mw]
  · iframe Hk Sw Mw
  have hn := hm.mem
  have ha885 := hm.funcs 885 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  simp only [cost469M]
  generalize hK : cost885M cfg code Kw Km = K
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

/-- The outer 872's state on the message path. -/
def StOutM (n ta : Nat) (A : Nat → Nat) (s : UInt32) (W : List UInt8 → IProp GF) (text : List UInt8)
    (x ip pp0 pv a0 pp argp kp k loc file flen line col : UInt32) (Xm : IProp GF) (fileB : List UInt8) (i : Nat) :
    IProp GF :=
  iprop(stk n ((s - 48).toNat - 304) 304 ∗ W (partOut text i) ∗
    (n ↦[i32][ x.toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
      XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB))

/-- The code the outer 872's writes run on the message path (persistent). -/
def COutM (cfg : WasmConfig) (lim : ExecLimits) (D DM inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (gt : GlobalType) (data vtab idx : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF)
    (B Kw : Nat) (pp argp kp k : UInt32) (Xm : IProp GF) (text : List UInt8) (Km Cg : Nat) : IProp GF :=
  iprop(A 469 ↪[wf] FuncInst.wasm types[13]! inst f469 ∗ A 885 ↪[wf] FuncInst.wasm types[13]! inst f885 ∗
    code885M inst mi A a code ∗ SinkW cfg lim D inst mi n g gt data code W B Kw Cg ∗
    MsgW cfg lim DM inst mi n g ta gt data vtab idx a W B pp argp kp k (XmT ta A Xm) text Km Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D DM inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (gt : GlobalType) (data vtab idx : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF)
    (B Kw : Nat) (pp argp kp k : UInt32) (Xm : IProp GF) (text : List UInt8) (Km Cg : Nat) :
    Persistent (COutM cfg lim D DM inst mi A n g ta gt data vtab idx a code W B Kw pp argp kp k Xm text Km Cg) := by
  unfold COutM; infer_instance

noncomputable def KB469M (cfg : WasmConfig) (code : Func) (Kw Km : Nat) : Nat :=
  activationGas cfg.regularOpCost (entryLocals f469 [.i32 0, .i32 0]) + cost469M cfg code Kw Km

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp872` for `to_string`'s `format_args!("{}", info)`** on the message path. -/
theorem hyp_outM (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D DM : Nat) (hdD : d + 8 ≤ D) (hdM : d + 5 ≤ DM)
    (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s data vtab idx argp0 x ip pp0 pv a0 pp argp kp k loc file flen line col : UInt32) (a : Nat)
    (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (Xm : IProp GF) (Km : Nat) (text fileB : List UInt8)
    (hs : 352 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (ha0 : a0 ≠ 0) (ha0b : a0.toNat + 24 ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (hwB : (panicText text fileB line.toNat col.toNat).length ≤ B) :
    Hyp872 (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1054332 argp0 1 (fun _ => 1054332)
      (fun _ => 0) (fun _ => x) (fun _ => 104) (fun _ => A 469) (fun _ => f469) a code
      (COutM cfg lim D DM inst mi A n g ta gt data vtab idx a code W B Kw pp argp kp k Xm text Km Cg)
      (MOut n ta A argp0 x)
      (StOutM n ta A s W (panicText text fileB line.toNat col.toNat) x ip pp0 pv a0 pp argp kp k loc file flen
        line col Xm fileB)
      Kw (cost469M cfg code Kw Km) (KB469M cfg code Kw Km) := by
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
    iunfold COutM, code885M at C
    icases C with ⟨-, -, ⟨#Hi, -, -, -, -, -, -, -, -, #Ha⟩, -⟩
    iframe Hi Ha
  · intro j hj
    rcases hj1 j hj
    simp only [StOutM, Nat.reduceMul]
    iintro #C
    iunfold COutM at C
    icases C with ⟨-, -, -, #Sw, -⟩
    iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1054332 0 304
      (partOut (panicText text fileB line.toNat col.toNat) 0) (partOut (panicText text fileB line.toNat col.toNat) 1)
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
    iunfold COutM at C
    icases C with ⟨#H469, -⟩
    iexact H469
  · intro j hj
    rcases hj1 j hj
    simp only [StOutM, Nat.reduceMul, Nat.reduceAdd]
    iintro #C
    iunfold COutM at C
    icases C with ⟨-, #H885, #Hk, #Sw, #Mw⟩
    ihave #S := f469_msg cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm D DM (by omega) (by omega) (by omega)
      Cg gt (s - 48) (s - 48 + 8) data vtab idx x ip pp0 pv a0 pp argp kp k loc file flen line col a code W B Kw
      Xm Km [] text fileB (by omega) (by omega) (by omega) hvt hip hloc ha0 ha0b hfl hfile hline hcol
      (by simpa using hwB) $$ [H885 Hk Sw Mw]
    · iframe H885 Hk Sw Mw
    simp only [partOut, List.nil_append]
    iexact S
  · intro j hj
    rcases hj1 j hj
    unfold KB469M; omega

/-! ## `to_string` (470) -/

/-- What `to_string` reads besides the `PanicInfo` on the message path: `XMsg`, the allocator's
vtable slot and the heap, the sink's vtable slot and the table entries 157 (759) and 104 (469), the
piece `""` at 1054332. -/
def toStrEnvM (n ta : Nat) (A : Nat → Nat) (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (idx : UInt32)
    (a0 pp argp kp k loc file flen line col : UInt32) (Xm : IProp GF) (fileB : List UInt8) : IProp GF :=
  iprop(XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB ∗ vt n 1057464 idx ta (A 578) ∗
    heapInv n maxP hl live F ∗
    (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
      ta ↦[wt][ (104 : UInt32).toNat ] Ref.func (A 469)) ∗
    (n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 ] 1054332 ∗ n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 + 4 ] 0))

/-- The code `to_string` runs on the message path (persistent). -/
def codeTSM (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(sinkCodeR n maxP inst mi A ∗ code885M inst mi A (A 759) f759 ∗
    A 759 ↪[wf] FuncInst.wasm types[15]! inst f759 ∗
    A 469 ↪[wf] FuncInst.wasm types[13]! inst f469 ∗ A 885 ↪[wf] FuncInst.wasm types[13]! inst f885 ∗
    A 746 ↪[wf] FuncInst.wasm types[13]! inst f746 ∗ A 471 ↪[wf] FuncInst.wasm types[0]! inst f471)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (codeTSM (GF := GF) n maxP inst mi A) := by
  unfold codeTSM; infer_instance

/-- `to_string`'s cost on a `PanicInfo` with a message. -/
noncomputable def costTSM (cfg : WasmConfig) (F J B Km : Nat) : Nat :=
  200 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f746 [.i32 0, .i32 0]) +
    activationGas cfg.regularOpCost (entryLocals f471 [.i32 0]) +
    activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
    costN cfg f759 (costHS cfg F J B B) (KB469M cfg f759 (costHS cfg F J B B) Km) 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`info.to_string()` (470) on a `PanicInfo` with a message**: `PanicHook.ToStr` with the bytes
`panicText text file line col`, given `MsgW` on `to_string`'s sink (`hMsg`). -/
theorem toStr_msg (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 27 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s ip pp0 pv a0 pp argp kp k loc file flen line col idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsS : S ≤ s.toNat)
    (hs2 : s.toNat + 28 ≤ 2 ^ 32)
    (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (ha0 : a0 ≠ 0) (ha0b : a0.toNat + 24 ≤ 2 ^ 32) (Xm : IProp GF) (Km : Nat)
    (text fileB : List UInt8)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J : Nat)
    (HG : HsGlobal maxP L0 F J (panicText text fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (Fr : IProp GF)
    (hMsg : ∀ (dd : UInt32) (W : List UInt8 → IProp GF),
      codeTSM n maxP inst mi A ∗
        SinkW cfg lim (lim.maxCallDepth - 17) inst mi n g gt dd f759 W
          (panicText text fileB line.toNat col.toNat).length
          (costHS cfg F J (panicText text fileB line.toNat col.toNat).length
            (panicText text fileB line.toNat col.toNat).length) Cg ⊢
        MsgW cfg lim (lim.maxCallDepth - 20) inst mi n g ta gt dd 1065404 157 (A 759) W
          (panicText text fileB line.toNat col.toNat).length pp argp kp k (XmT ta A Xm) text Km Cg) :
    codeTSM n maxP inst mi A ⊢
      ToStr (GF := GF) cfg lim d inst mi Cg n g gt s ip S
        iprop(infoCells n ip pp0 pv a0 loc ∗
          (toStrEnvM n ta A maxP hl live F idx a0 pp argp kp k loc file flen line col Xm fileB ∗ Fr))
        (costTSM cfg F J (panicText text fileB line.toNat col.toNat).length Km)
        (panicText text fileB line.toNat col.toNat) := by
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
  iunfold codeTSM at Hc1
  icases Hc1 with ⟨#Hsk, #Hk885, #H759, #H469, #H885, #H746, #H471⟩
  ihave #Hk' := Hk885
  iunfold code885M at Hk'
  icases Hk' with ⟨#Hi, #H872, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha746 := hm.funcs 746 (by decide)
  have ha471 := hm.funcs 471 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  ihave #Sw := hsink_sinkW (GF := GF) cfg lim inst mi A n g ta hm Cg gt maxP L0 live F J
    (panicText text fileB line.toNat col.toNat).length (s + 16) idx
    (s - 48 - 32 + 4) HG (by omega) (by omega) hlim $$ Hsk
  ihave #Mw := hMsg (s - 48 - 32 + 4)
    (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
      hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
    $$ [Hc0 Sw]
  · iframe Hc0 Sw
  ihave #Co : COutM cfg lim (lim.maxCallDepth - 17) (lim.maxCallDepth - 20) inst mi A n g ta gt
      (s - 48 - 32 + 4) 1065404 157 (A 759) f759
      (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
      (panicText text fileB line.toNat col.toNat).length
      (costHS cfg F J (panicText text fileB line.toNat col.toNat).length
        (panicText text fileB line.toNat col.toNat).length) pp argp kp k Xm text Km Cg $$ [H469 H885 Hk885 Sw Mw]
  · iunfold COutM; iframe H469 H885 Hk885 Sw Mw
  -- the outer 872 in the shape `f746_gen` asks
  have S872 := f872_gen (GF := GF) cfg lim (d + 1 + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 48 - 32) (s - 48 - 32 + 4) 1065404 (s - 48 - 32 + 8) 1054332 (s - 48 + 40) 157 1 (by decide) (by omega)
    (by simp [UInt32.toNat_add, h80]; omega) (by simp) (by simp; omega)
    (fun _ => 1054332) (fun _ => 0) (fun _ => s - 48 + 12) (fun _ => 104) (fun _ => A 469) (fun _ => f469) (A 759) f759
    (COutM cfg lim (lim.maxCallDepth - 17) (lim.maxCallDepth - 20) inst mi A n g ta gt
      (s - 48 - 32 + 4) 1065404 157 (A 759) f759
      (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
      (panicText text fileB line.toNat col.toNat).length
      (costHS cfg F J (panicText text fileB line.toNat col.toNat).length
        (panicText text fileB line.toNat col.toNat).length) pp argp kp k Xm text Km Cg)
    (MOut n ta A (s - 48 + 40) (s - 48 + 12))
    (StOutM n ta A (s - 48 - 32)
      (fun w => iprop(n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) w))
      (panicText text fileB line.toNat col.toNat) (s - 48 + 12) ip pp0 pv a0 pp argp kp k loc file flen line col
      Xm fileB)
    (costHS cfg F J (panicText text fileB line.toNat col.toNat).length
      (panicText text fileB line.toNat col.toNat).length)
    (cost469M cfg f759 (costHS cfg F J (panicText text fileB line.toNat col.toNat).length
      (panicText text fileB line.toNat col.toNat).length) Km)
    (KB469M cfg f759 (costHS cfg F J (panicText text fileB line.toNat col.toNat).length
      (panicText text fileB line.toNat col.toNat).length) Km)
    (hyp_outM cfg lim (d + 1 + 1) inst mi A n g ta hm (lim.maxCallDepth - 17) (lim.maxCallDepth - 20) (by omega)
      (by omega) (by omega) Cg gt
      (s - 48 - 32) (s - 48 - 32 + 4) 1065404 157 (s - 48 + 40) (s - 48 + 12) ip pp0 pv a0 pp argp kp k loc file
      flen line col (A 759) f759 _ _ _ Xm Km text fileB (by omega) (by omega) (by decide) hip hloc ha0 ha0b hfl
      hfile hline hcol le_rfl)
  rw [show 2 * (1 : UInt32).toNat = 2 from rfl] at S872
  have S872' := S872.trans (MFunSpec_frame (GF := GF) (Fr := iprop(emp))
    (P' := fun args => iprop(⌜args = [.i32 (s - 48 - 32 + 4), .i32 1065404, .i32 (s - 48 - 32 + 8)]⌝ ∗
      g ↦[wg] ⟨gt, .i32 (s - 48 - 32)⟩ ∗ argsAt n (s - 48 - 32 + 8) 1054332 (s - 48 + 40) ∗
      n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
      (stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) [] ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
          XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB))))
    (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 48 - 32)⟩ ∗
      argsAt n (s - 48 - 32 + 8) 1054332 (s - 48 + 40) ∗ n ↦[i32][ (s - 48 - 32 + 4).toNat ] (s + 16) ∗
      (stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578)
          (panicText text fileB line.toNat col.toNat) ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
          XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB))))
    (fun args => by
      iintro ⟨%ha, Hg, HA, Hd, Hs, HM, ⟨V157, T157⟩, HS, HX⟩
      icases stkSp 304 48 rfl $$ Hs with ⟨Hs1, Hs2⟩
      isplitl
      · iframe Hg HM V157 T157
        isplitr; · ipureintro; exact ha
        isplitl [Hs2]; · iapply stkA (by omega) $$ Hs2
        isplitl [HA]; · iunfold argsAt at HA; iunfold argsN; iexact HA
        iunfold StOutM
        isplitl [Hs1]; · iapply stkA (by omega) $$ Hs1
        simp only [partOut]
        iframe Hd HS HX
      · iempintro)
    (fun args rs => by
      iintro ⟨-, %hrs, Hg, Hs2, HA, HM, V157, T157, HSt⟩
      iunfold StOutM at HSt
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
  simp only [costTSM]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hout, HI, HE, -⟩
  subst hargs
  iunfold toStrEnvM at HE
  icases HE with ⟨HXP, Hvt, Hh, ⟨V157, T157, T104⟩, ⟨P0, P4⟩⟩
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
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578) [] ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
          XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB))
    iprop(stk n ((s - 48 - 32).toNat - 352) 352 ∗ MOut n ta A (s - 48 + 40) (s - 48 + 12) ∗
        (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759)) ∗
        hsink n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta (A 578)
          (panicText text fileB line.toNat col.toNat) ∗
        (n ↦[i32][ (s - 48 + 12).toNat ] ip ∗ infoCells n ip pp0 pv a0 loc ∗
          XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB))
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
  ihave HS := hsink_init n maxP L0 live F J (panicText text fileB line.toNat col.toNat).length (s + 16) idx ta
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
  icases splitB (a := ptr.toNat) (b := ptr.toNat + (panicText text fileB line.toNat col.toNat).length)
    (panicText text fileB line.toNat col.toNat) rest rfl $$ Hb with ⟨Hb, -⟩
  iframe Hb
  isplitl [V0]; · iapply memBytes_addr _ $$ V0; omega
  isplitl [V4]; · iapply memBytes_addr _ $$ V4; omega
  iapply memBytes_addr _ $$ V8; omega

end Spec

end WNear.Binary.ToStrMsg
