import Bridge.Functions.PanicMsg

/-!
# `<PanicInfo as Display>::fmt` (885) on a `PanicInfo` with a message

```wat
;; 885 (info, f)                           sp -= 64
(f.vtable.write_str)(f.data, "panicked at ")
msg := [info + 8]  (≠ 0: the message path)
[sp+12] := msg;  args [(sp + 12, 202)] at sp + 16      ;; 202: 887, <&Arguments as Display>
core::fmt::write(f.data, f.vtable, Arguments { pieces: ["'", "', "] (1070688), fmt: None, args })
then the location, as on the payload path
```

`f885_msg`: on the `PanicInfo` at `ip` with the message `a0` (the `Arguments` whose header is
`argsH n a0 pp argp kp k`) and the location `loc`, the writer `W` (`SinkW`) gets
`panicText text file line col`, `text` what the message's `Arguments` format to (`PanicMsg.MsgW`).
The message's 872 is `FmtWriteT.f872_tr` on `PanicMsg.hypA_msg`, the location's `FmtWriteN.f872_gen`
on `hypB_loc`. Stack: 885's frame of 64 bytes and 240 below it.
-/

namespace WNear.Binary.PanicDisplayMsg

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtWriteN (fmtrP Hyp872 argsN costN f872_gen)
open WNear.Binary.FmtWriteT (Hyp872T argsT costT f872_tr)
open WNear.Binary.PanicHook (stk4_word stk_split')
open WNear.Binary.PanicWithHook (infoCells)
open WNear.Binary.PanicText (panicText b)
open WNear.Binary.PanicDisplay
open WNear.Binary.PanicMsg
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 885 runs on the message path (persistent). -/
def code885M (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (a : Nat) (code : Func) : IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
    A 887 ↪[wf] FuncInst.wasm types[13]! inst f887 ∗
    A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗ A 880 ↪[wf] FuncInst.wasm types[13]! inst f880 ∗
    A 870 ↪[wf] FuncInst.wasm types[13]! inst f870 ∗ A 936 ↪[wf] FuncInst.wasm types[68]! inst f936 ∗
    A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
    a ↪[wf] FuncInst.wasm types[15]! inst code)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (a : Nat) (code : Func) :
    Persistent (code885M (GF := GF) inst mi A a code) := by
  unfold code885M; infer_instance

/-- The table entry 195 (880) with `Xm`: the message's `Arguments` and the location share it. -/
def XmT (ta : Nat) (A : Nat → Nat) (Xm : IProp GF) : IProp GF :=
  iprop(ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ Xm)

/-- What 885 reads on the message path besides the `PanicInfo`: the pieces and their arrays, the
table entries, the message's header and `Xm`, the location's. -/
def XMsg (n ta : Nat) (A : Nat → Nat) (a0 pp argp kp k loc file flen line col : UInt32) (Xm : IProp GF)
    (fileB : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1070672 ] pk12 ∗
    ((n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 ] pptrA 0 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 + 4 ] plenA 0) ∗
      (n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 ] pptrA 1 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 + 4 ] plenA 1) ∗
      ta ↦[wt][ (202 : UInt32).toNat ] Ref.func (A 887)) ∗
    ((n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 ] pptrB 0 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 + 4 ] plenB 0) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 ] pptrB 1 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 + 4 ] plenB 1) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 ] pptrB 2 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 + 4 ] plenB 2) ∗
      ta ↦[wt][ (3 : UInt32).toNat ] Ref.func (A 870)) ∗
    (n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗
    (argsH n a0 pp argp kp k ∗ XmT ta A Xm) ∗
    XB n loc file flen line col fileB)

/-- 885's cost on the message path, the activation excluded. -/
noncomputable def cost885M (cfg : WasmConfig) (code : Func) (Kw Km : Nat) : Nat :=
  300 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) + Kw +
    2 * activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
    costT cfg code Kw (KBM cfg Km) 1 + costN cfg code Kw (KBB cfg code Kw) 3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`<PanicInfo as Display>::fmt(ip, f)`** (885) on a `PanicInfo` with the message `a0`:
`panicText text file line col` appended to the writer. -/
theorem f885_msg (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (D DM : Nat) (hdD : d + 6 ≤ D) (hdM : d + 3 ≤ DM) (hd : d + 7 < lim.maxCallDepth)
    (Cg : Nat)
    (gt : GlobalType) (s f data vtab idx ip pp0 pv a0 pp argp kp k loc file flen line col : UInt32)
    (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat) (Xm : IProp GF) (Km : Nat)
    (w0 text fileB : List UInt8)
    (hs : 304 ≤ s.toNat) (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hf : f.toNat + 32 ≤ 2 ^ 32)
    (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (ha0 : a0 ≠ 0) (ha0b : a0.toNat + 24 ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (hwB : w0.length + (panicText text fileB line.toNat col.toNat).length ≤ B) :
    code885M inst mi A a code ∗ SinkW cfg lim D inst mi n g gt data code W B Kw Cg ∗
      MsgW cfg lim DM inst mi n g ta gt data vtab idx a W B pp argp kp k (XmT ta A Xm) text Km Cg
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f885 Cg
        (fun args => iprop(⌜args = [.i32 ip, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗
          fmtrP n ta f data vtab idx a ∗ infoCells n ip pp0 pv a0 loc ∗
          XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB ∗ W w0))
        (fun _ => cost885M cfg code Kw Km)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 304) 304 ∗
          fmtrP n ta f data vtab idx a ∗ infoCells n ip pp0 pv a0 loc ∗
          XMsg n ta A a0 pp argp kp k loc file flen line col Xm fileB ∗
          W (w0 ++ panicText text fileB line.toNat col.toNat))) := by
  iintro ⟨#Hk, #Sw, #Mw⟩
  ihave #Hk' := Hk
  iunfold code885M at Hk'
  icases Hk' with ⟨#Hi, #H872, #H887, #H856, #H880, #H870, #H936, #H903, #H910, #Ha⟩
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hty15 : types[15]! = mi.types[15]! := by rw [hm.types]
  have ha872 := hm.funcs 872 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h64 : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hDl := FmtDigits.decDigits_length_le 5 line.toNat (by omega) (by simp; omega)
  have hDc := FmtDigits.decDigits_length_le 5 col.toNat (by omega) (by simp; omega)
  have hPT : (panicText text fileB line.toNat col.toNat).length =
      16 + text.length + fileB.length + 2 + (decDigits line.toNat).length + (decDigits col.toNat).length := by
    have e1 : (b "panicked at ").length = 12 := by decide +kernel
    have e2 : (b "'").length = 1 := by decide +kernel
    have e3 : (b "', ").length = 3 := by decide +kernel
    have e4 : (b ":").length = 1 := by decide +kernel
    simp only [panicText, List.length_append, e1, e2, e3, e4]; omega
  ihave #Sw' := Sw
  iunfold SinkW at Sw'
  ihave #S0 := Sw' $$ %(d + 1) %(s - 64) %1070672 %12 %w0 %pk12 %⟨by omega, by omega, pk12_length, by simp,
    by rw [hPT] at hwB; simp; omega⟩
  simp only [cost885M]
  generalize hACT : activationGas cfg.regularOpCost (entryLocals code [.i32 0, .i32 0, .i32 0]) = ACT
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HF, HI, HX, HW⟩
  subst hargs
  iunfold infoCells at HI
  icases HI with ⟨I0, I4, I8, I12⟩
  iunfold XMsg at HX
  icases HX with ⟨Hpk, PA, PB, PQ, HAm, HXB⟩
  iunfold fmtrP, fmtr at HF
  icases HF with ⟨⟨F0, F8, F24, F28, V12, Ht⟩, F16⟩
  -- the stack: 240 bytes below the frame, the frame's words
  ihave Hs := stk_addr (show s.toNat - 304 = (s - 64).toNat - 240 by omega) $$ Hs
  icases stk_split' n _ 304 240 64 rfl $$ Hs with ⟨Lo, Fr⟩
  ihave Fr := stk_addr (show (s - 64).toNat - 240 + 240 = (s - 64).toNat by omega) $$ Fr
  icases stk_split' n _ 64 12 52 rfl $$ Fr with ⟨X0, Fr⟩
  icases stk_split' n _ 52 4 48 rfl $$ Fr with ⟨W12, Fr⟩
  icases stk_split' n _ 48 4 44 rfl $$ Fr with ⟨W16, Fr⟩
  icases stk_split' n _ 44 4 40 rfl $$ Fr with ⟨W20, Fr⟩
  icases stk_split' n _ 40 4 36 rfl $$ Fr with ⟨W24, Fr⟩
  icases stk_split' n _ 36 4 32 rfl $$ Fr with ⟨W28, Fr⟩
  icases stk_split' n _ 32 4 28 rfl $$ Fr with ⟨W32, Fr⟩
  icases stk_split' n _ 28 4 24 rfl $$ Fr with ⟨W36, Fr⟩
  icases stk_split' n _ 24 4 20 rfl $$ Fr with ⟨W40, Fr⟩
  icases stk_split' n _ 20 8 12 rfl $$ Fr with ⟨W44, Fr⟩
  icases stk_split' n _ 12 4 8 rfl $$ Fr with ⟨X52, Fr⟩
  icases stk_split' n _ 8 4 4 rfl $$ Fr with ⟨W56, W60⟩
  icases stk4_word n _ $$ W12 with ⟨%o12, W12⟩
  icases stk4_word n _ $$ W16 with ⟨%o16, W16⟩
  icases stk4_word n _ $$ W20 with ⟨%o20, W20⟩
  icases stk4_word n _ $$ W24 with ⟨%o24, W24⟩
  icases stk4_word n _ $$ W28 with ⟨%o28, W28⟩
  icases stk4_word n _ $$ W32 with ⟨%o32, W32⟩
  icases stk4_word n _ $$ W36 with ⟨%o36, W36⟩
  icases stk4_word n _ $$ W40 with ⟨%o40, W40⟩
  icases stk4_word n _ $$ W56 with ⟨%o56, W56⟩
  icases stk4_word n _ $$ W60 with ⟨%o60, W60⟩
  iunfold stk at W44
  icases W44 with ⟨%o44, %ho44, W44⟩
  icases stkSp 128 112 rfl $$ Lo with ⟨Lo1, Lo2⟩
  ihave Lo2 := stkA (show (s - 64).toNat - 240 + 128 = (s - 64).toNat - 112 by omega) $$ Lo2
  ihave Hpk := memBytes_addr (show 1070672 = (1070672 : UInt32).toNat from rfl) $$ Hpk
  simp only [f885]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [F28]
  mstep [V12]
  -- "panicked at "
  iapply mwpi_cons
  rw [show [Value.i32 data, Value.i32 1070672, Value.i32 12, Value.i32 idx] =
    [Value.i32 data, Value.i32 1070672, Value.i32 12] ++ [Value.i32 idx] from rfl]
  iapply mwpi_call_indirect_spec_args (R := 280 * cfg.regularOpCost + 28 * cfg.regularOpCost +
      costT cfg code Kw (KBM cfg Km) 1 + costN cfg code Kw (KBB cfg code Kw) 3 + R) 15 0 ta idx a types[15]!
    inst mi code [.i32 data, .i32 1070672, .i32 12] _ (fun _ => Kw) _ hta hty15 rfl (by omega)
  rw [FmtU64.act3, hACT]
  isplitl [Hc]
  · iapply credits_le; iframe Hc; ipureintro; omega
  isplitl [Ht]; · iexact Ht
  isplitr; · iexact Ha
  isplitr; · iexact Hi
  isplitr; · iexact S0
  isplitl [Hg Lo2 HW Hpk]
  · iframe Hg Lo2 HW Hpk; ipureintro; rfl
  inext
  iintro %rs Ht Hc HQ
  icases HQ with ⟨%hrs, Hg, Lo2, HW, Hpk⟩
  subst hrs
  mstep_post
  repeat mstep
  mstep [I8]
  mstep
  mstep_taken with (simp [ha0])
  repeat mstep
  mstep [W12]
  repeat mstep
  mstep [W20]
  repeat mstep
  mstep [W16]
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [F28]
  repeat mstep
  mstep [W60]
  repeat mstep
  mstep [W44]
  rw [i64_2] at *
  repeat mstep
  mstep [W40]
  repeat mstep
  mstep [W56]
  repeat mstep
  -- the message: 872 on `hypA_msg`
  have h16 : (s - 64 + 16).toNat = (s - 64).toNat + 16 := by simp [UInt32.toNat_add, h64]; omega
  have h12 : (s - 64 + 12).toNat = (s - 64).toNat + 12 := by simp [UInt32.toNat_add, h64]; omega
  have h40 : (s - 64 + 40).toNat = (s - 64).toNat + 40 := by simp [UInt32.toNat_add, h64]; omega
  have h48' : (s - 64 - 48).toNat = (s - 64).toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  ihave #CMh : CM cfg lim D DM inst mi A n g ta gt data vtab idx a code W B Kw pp argp kp k (XmT ta A Xm) text Km Cg
    $$ [Hi H887 H872 Ha Sw Mw]
  · iunfold CM; iframe Hi H887 H872 Ha Sw Mw
  have SA := f872_tr (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 64) data
    vtab (s - 64 + 40) 1070688 (s - 64 + 16) idx 2 1 (by decide) (by decide) (by omega) (by omega) (by simp)
    (by simp; omega) pptrA plenA (fun _ => s - 64 + 12) (fun _ => 202) (fun _ => A 887) (fun _ => f887) a code
    (CM cfg lim D DM inst mi A n g ta gt data vtab idx a code W B Kw pp argp kp k (XmT ta A Xm) text Km Cg)
    (MM n ta A (s - 64 + 16) (s - 64 + 12))
    (StM n (s - 64) W (w0 ++ pk12) (s - 64 + 12) a0 pp argp kp k (XmT ta A Xm) text) Kw (cost887 cfg + Km) (KBM cfg Km)
    (hypA_msg cfg lim (d + 1) inst mi A n g ta hm D DM (by omega) (by omega) (by omega) Cg gt (s - 64) data vtab idx
      (s - 64 + 16) (s - 64 + 12) a0 pp argp kp k a code W B Kw (XmT ta A Xm) text Km (w0 ++ pk12) (by omega) (by omega)
      ha0b (by simp only [List.length_append, pk12_length]; rw [hPT] at hwB; omega))
  rw [show 2 * (1 : UInt32).toNat + 1 = 3 from rfl] at SA
  ihave #SA' := SA $$ CMh
  ihave Lo := stk_join n _ 128 112 $$ [Lo1 Lo2]
  · iframe Lo1; iapply stk_addr _ $$ Lo2; omega
  icases stk_split' n _ 240 192 48 rfl $$ Lo with ⟨LoA, LoF⟩
  icases (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 2) (bytes32 0)).1 $$ W44 with ⟨W44, W48⟩
  icases PA with ⟨PA0, PA1, T202⟩
  mcall SA' using [Hg LoF W40 W44 W48 W56 W60 PA0 PA1 T202 W16 W20 HW PQ W12 HAm LoA V12 Ht]
  · iframe Hg V12 Ht
    isplitl [LoF]
    · iapply stk_addr _ $$ LoF; omega
    isplitl [W40 W44 W48 W56 W60]
    · iunfold argsT
      rw [h40]
      isplitl [W40]; · iapply memBytes_addr _ $$ W40; omega
      isplitl [W44]; · iapply memBytes_addr _ $$ W44; omega
      isplitl [W48]; · iapply memBytes_addr _ $$ W48; simp [bytes32] <;> omega
      isplitl [W56]; · iapply memBytes_addr _ $$ W56; omega
      iapply memBytes_addr _ $$ W60; omega
    isplitl [PA0 PA1 T202 W16 W20]
    · iunfold MM
      simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]
      iframe PA0 PA1 T202
      rw [h16]
      isplitl [W16]; · iapply memBytes_addr _ $$ W16; omega
      iapply memBytes_addr _ $$ W20; omega
    iunfold StM
    isplitl [LoA]
    · iapply stk_addr _ $$ LoA; omega
    isplitl [HW]
    · simp only [partA, List.append_nil]; iexact HW
    iunfold XM
    icases HAm with ⟨HAh, HXm⟩
    iframe PQ HAh HXm
    rw [h12]
    iapply memBytes_addr _ $$ W12; omega
  icases HQ with ⟨%hrs, Hg, LoF, HA, HM, V12, Ht, HSt⟩
  subst hrs
  repeat mstep
  -- the location's arguments
  iunfold argsT at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  iunfold MM at HM
  icases HM with ⟨PA0, PA1, M0, M4, T202⟩
  ihave A0 := memBytes_addr (show (s - 64 + 40).toNat = (s - 64).toNat + 40 by omega) $$ A0
  ihave A8 := memBytes_addr (show (s - 64 + 40).toNat + 8 = (s - 64).toNat + 44 + (bytes32 2).length by
    simp [bytes32]; omega) $$ A8
  ihave A4 := memBytes_addr (show (s - 64 + 40).toNat + 4 = (s - 64).toNat + 44 by omega) $$ A4
  ihave A48 := (memBytes_append (GF := GF) (H := NearState) n ((s - 64).toNat + 44) (bytes32 2) (bytes32 0)).2
    $$ [A4 A8]
  · iframe A4 A8
  ihave A16 := memBytes_addr (show (s - 64 + 40).toNat + 16 = (s - 64).toNat + 56 by omega) $$ A16
  ihave A20 := memBytes_addr (show (s - 64 + 40).toNat + 20 = (s - 64).toNat + 60 by omega) $$ A20
  ihave M0 := memBytes_addr (show (s - 64 + 16).toNat + 8 * 0 = (s - 64).toNat + 16 by omega) $$ M0
  ihave M4 := memBytes_addr (show (s - 64 + 16).toNat + 8 * 0 + 4 = (s - 64).toNat + 20 by omega) $$ M4
  mstep [I12]
  repeat mstep
  mstep [W36]
  repeat mstep
  mstep [W28]
  repeat mstep
  mstep [W32]
  repeat mstep
  mstep [W24]
  repeat mstep
  mstep [M4]
  repeat mstep
  mstep [M0]
  repeat mstep
  mstep [F24]
  repeat mstep
  mstep [F28]
  repeat mstep
  mstep [A20]
  repeat mstep
  mstep [A48]
  rw [i64_3] at *
  repeat mstep
  mstep [A0]
  repeat mstep
  mstep [A16]
  repeat mstep
  -- the location: 872 on `hypB_loc`
  ihave #CBh : CB cfg lim D inst mi A n g gt data a code W B Kw Cg $$ [Hi H856 H880 H870 H936 H903 H910 Ha Sw]
  · iunfold CB; iframe Hi H856 H880 H870 H936 H903 H910 Ha Sw
  have hA3 : (partA text 3).length = text.length + 4 := by simp [partA, qp, qcp] <;> omega
  have SB := f872_gen (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 64) data
    vtab (s - 64 + 40) 1070708 (s - 64 + 16) idx 3 (by decide) (by omega) (by omega) (by simp <;> omega) (by simp <;> omega)
    pptrB plenB (vpB loc) fiB (bB A) codeBB a code (CB cfg lim D inst mi A n g gt data a code W B Kw Cg)
    (MB n ta A (s - 64 + 16) loc) (StB n (s - 64) W ((w0 ++ pk12) ++ partA text 3) loc file flen line col fileB)
    Kw (KbB cfg code Kw) (KBB cfg code Kw)
    (hypB_loc cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 64) data vtab idx
      (s - 64 + 16) loc file flen line col a code W B Kw ((w0 ++ pk12) ++ partA text 3) fileB (by omega) (by omega)
      hvt hloc hfl hfile hline hcol
      (by simp only [List.length_append, pk12_length, hA3]; rw [hPT] at hwB; omega))
  rw [show 2 * (3 : UInt32).toNat = 6 from rfl] at SB
  ihave #SB' := SB $$ CBh
  iunfold StM at HSt
  icases HSt with ⟨LoA, HW, HXA⟩
  iunfold XM at HXA
  icases HXA with ⟨PQ, Y12, HAh, HXmT⟩
  iunfold XmT at HXmT
  icases HXmT with ⟨T195, HXm⟩
  icases stk_split' n _ 192 32 160 rfl $$ LoA with ⟨Lo0, LoB⟩
  icases (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 3) (bytes32 0)).1 $$ A48 with ⟨A4, A8⟩
  icases PB with ⟨PB0, PB1, PB2, T3⟩
  mcall SB' using [Hg LoF A0 A4 A8 A16 A20 PB0 PB1 PB2 T195 T3 M0 M4 W24 W28 W32 W36 V12 Ht LoB HW HXB]
  · iframe Hg V12 Ht
    isplitl [LoF]
    · iapply stk_addr _ $$ LoF; omega
    isplitl [A0 A4 A8 A16 A20]
    · iunfold argsN
      rw [h40]
      isplitl [A0]; · iapply memBytes_addr _ $$ A0; omega
      isplitl [A4]; · iapply memBytes_addr _ $$ A4; omega
      isplitl [A8]; · iapply memBytes_addr _ $$ A8; simp [bytes32] <;> omega
      isplitl [A16]; · iapply memBytes_addr _ $$ A16; omega
      iapply memBytes_addr _ $$ A20; omega
    isplitl [PB0 PB1 PB2 T195 T3 M0 M4 W24 W28 W32 W36]
    · iunfold MB
      simp only [vpB, fiB, UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, ↓reduceIte,
        Nat.reduceEqDiff]
      iframe PB0 PB1 PB2 T195 T3
      rw [h16]
      isplitl [M0 M4]
      · isplitl [M0]; · iapply memBytes_addr _ $$ M0; omega
        iapply memBytes_addr _ $$ M4; omega
      isplitl [W24 W28]
      · isplitl [W24]; · iapply memBytes_addr _ $$ W24; omega
        iapply memBytes_addr _ $$ W28; omega
      isplitl [W32]; · iapply memBytes_addr _ $$ W32; omega
      iapply memBytes_addr _ $$ W36; omega
    iunfold StB
    isplitl [LoB]
    · iapply stk_addr _ $$ LoB; omega
    iframe HXB
    simp only [partB, List.append_nil]; iexact HW
  icases HQ with ⟨%hrs, Hg, LoF, HA, HM, V12, Ht, HSt⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  repeat mstep
  rw [show s - 64 + 64 = s by simp]
  mcredits R
  iframe Hc Hg
  isplitr
  · ipureintro; rw [htype]; rfl
  iunfold StB at HSt
  icases HSt with ⟨LoB, HW, HXB⟩
  iunfold argsN at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  iunfold MB at HM
  icases HM with ⟨PB0, PB1, PB2, ⟨M0, M4⟩, ⟨M8, M12⟩, ⟨M16, M20⟩, T195, T3⟩
  isplitl [Lo0 LoB LoF X0 Y12 M0 M4 M8 M12 M16 M20 A0 A4 A8 X52 A16 A20]
  · ihave Fr := frame64 n (s - 64).toNat $$ [X0 Y12 M0 M4 M8 M12 M16 M20 A0 A4 A8 X52 A16 A20]
    · iframe X0
      isplitl [Y12]; · iapply memBytes_addr _ $$ Y12; omega
      isplitl [M0]; · iapply memBytes_addr _ $$ M0; omega
      isplitl [M4]; · iapply memBytes_addr _ $$ M4; omega
      isplitl [M8]; · iapply memBytes_addr _ $$ M8; omega
      isplitl [M12]; · iapply memBytes_addr _ $$ M12; omega
      isplitl [M16]; · iapply memBytes_addr _ $$ M16; omega
      isplitl [M20]; · iapply memBytes_addr _ $$ M20; omega
      isplitl [A0]; · iapply memBytes_addr _ $$ A0; omega
      isplitl [A4]; · iapply memBytes_addr _ $$ A4; omega
      isplitl [A8]; · iapply memBytes_addr _ $$ A8; omega
      isplitl [X52]; · iapply stk_addr _ $$ X52; omega
      isplitl [A16]; · iapply memBytes_addr _ $$ A16; omega
      iapply memBytes_addr _ $$ A20; omega
    ihave Lo := stk_join n ((s - 64).toNat - 240) 32 160 $$ [Lo0 LoB]
    · isplitl [Lo0]; · iapply stk_addr _ $$ Lo0; omega
      iapply stk_addr _ $$ LoB; omega
    ihave Lo := stk_join n ((s - 64).toNat - 240) 192 48 $$ [Lo LoF]
    · iframe Lo; iapply stk_addr _ $$ LoF; omega
    iapply stk_addr (show (s - 64).toNat - 240 = s.toNat - 304 by omega)
    iapply stk_join n ((s - 64).toNat - 240) 240 64
    iframe Lo
    iapply stk_addr _ $$ Fr; omega
  isplitl [F0 F8 F24 F28 V12 Ht F16]
  · iunfold fmtrP, fmtr; iframe F0 F8 F24 F28 V12 Ht F16
  isplitl [I0 I4 I8 I12]
  · iunfold infoCells; iframe I0 I4 I8 I12
  isplitl [Hpk PA0 PA1 T202 PB0 PB1 PB2 T195 T3 PQ HAh HXm HXB]
  · iunfold XMsg
    simp only [UInt32.reduceToNat]
    iframe PQ HAh HXB PB0 PB1 PB2 T3 PA0 PA1 T202
    isplitl [Hpk]; · iapply memBytes_addr _ $$ Hpk; rfl
    iunfold XmT; simp only [UInt32.reduceToNat]; iframe T195 HXm
  rw [← panicText_parts]
  simp only [List.append_assoc] at *
  iexact HW

end Spec

end WNear.Binary.PanicDisplayMsg
