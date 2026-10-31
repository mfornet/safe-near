import Bridge.Functions.PanicTotalHook
import Bridge.Functions.PanicWithHook
import Bridge.Functions.PanicFmt

namespace WNear.Binary.PanicTotal
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.PanicStr NearLogic.PanicUtf8Large
open WNear.Binary.Interface
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.PanicHook
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

open WNear.Binary.PanicWithHook
open WNear.Binary.SetupPanicHook (hookCells)
set_option maxHeartbeats 16000000 in
/-- Actual rust_panic_with_hook covers both message lengths, retaining exact payload Get and ToStr obligations. -/
theorem f824_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp p0 vt msg loc gidx : UInt32) (ag : Nat) (codeG : Func) (pp pv lpc : UInt32) (S : Nat)
    (hS : 32 ≤ S) (hsp : S + 64 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hvt : vt.toNat + 20 ≤ 2 ^ 32)
    (G G' D0 : IProp GF) (Kg K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    ag ↪[wf] FuncInst.wasm types[14]! inst codeG ∗
      GetSpec cfg lim (d + 1) inst mi Cg n g gt (sp - 32) p0 pp pv (S + 32) codeG G G' Kg ∗
      A 473 ↪[wf] FuncInst.wasm types[14]! inst f473 ∗ A 474 ↪[wf] FuncInst.wasm types[0]! inst f474 ∗
      hookCode e inst mi A n mx ∗
      ToStr cfg lim (d + 3) inst mi Cg n g gt (sp - 32 - 32) (sp - 32 + 16) S
        iprop(infoCells n (sp - 32 + 16) pp pv msg loc ∗ G' ∗ D0) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f824 Cg
        (PanicWithHook.pre n g ta A gt sp p0 vt msg loc gidx ag lpc S G D0 h)
        (fun _ => cost824 cfg codeG Kg K bs h) (fun _ _ => iprop(False)) (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#FG, #Sg, #F473, #F474, #Hcode, #Hts⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have e16 : (sp - 32 + 16).toNat = (sp - 32).toNat + 16 := by simp [UInt32.toNat_add]; omega
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold PanicWithHook.pre at HP
  icases HP with ⟨%hargs, Hg, Hs, HH, Vg, Tg, HG, HD0, HI, HS, Hh⟩
  subst hargs
  iunfold hookInstalled, hookCells at HH
  icases HH with ⟨⟨Gpc, Lk, Hd, Hv⟩, L0, L1, V12, T118⟩
  icases stk824 n sp S hsp $$ Hs with ⟨Hlo, -, H8, Hinfo⟩
  ihave Gpc := (memBytes_congr (j := (0 : UInt32).toNat + 1074932) (by simp)).1 $$ Gpc
  ihave Lk := (memBytes_congr (j := (0 : UInt32).toNat + 1074920) (by simp)).1 $$ Lk
  ihave Hd := (memBytes_congr (j := (0 : UInt32).toNat + 1074924) (by simp)).1 $$ Hd
  ihave Hv := (memBytes_congr (j := (0 : UInt32).toNat + 1074928) (by simp)).1 $$ Hv
  ihave L0 := (memBytes_congr (j := (0 : UInt32).toNat + 1074936) (by simp)).1 $$ L0
  simp only [f824, cost824]
  generalize hAG : activationGas cfg.regularOpCost (entryLocals codeG [.i32 0, .i32 0]) = AG
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  -- GLOBAL_PANIC_COUNT += 1
  mstep; mstep; mstep [Gpc]; mstep; mstep; mstep [Gpc]
  -- LOCAL_PANIC_COUNT: (1, 1)
  mstep; mstep; mstep
  mstep; mstep [L0]; mstep; mstep; mstep
  ihave L01 := (memBytes_append n 1074936 (bytes32 0) (bytes32 lpc)).2 $$ [L0 L1]
  · isplitl [L0]
    · iexact L0
    iapply memBytes_congr (by simp) |>.1 $$ L1
  mstep; mstep; mstep [L01]
  mstep
  -- the PanicInfo
  icases VecFromElem.stk16 n _ $$ Hinfo with ⟨I16, I20, I24, I28⟩
  icases stk4_word n _ $$ I16 with ⟨%i16, I16⟩
  icases stk4_word n _ $$ I20 with ⟨%i20, I20⟩
  icases stk4_word n _ $$ I24 with ⟨%i24, I24⟩
  icases stk4_word n _ $$ I28 with ⟨%i28, I28⟩
  ihave I20 := memBytes_congr (j := (sp - 32).toNat + 20) (by omega) |>.1 $$ I20
  ihave I24 := memBytes_congr (j := (sp - 32).toNat + 24) (by omega) |>.1 $$ I24
  ihave I28 := memBytes_congr (j := (sp - 32).toNat + 28) (by omega) |>.1 $$ I28
  mstep; mstep; mstep [I28]
  mstep; mstep; mstep [I24]
  mstep; mstep; mstep [I20]
  mstep; mstep; mstep [I16]
  -- HOOK_LOCK: free, read-locked
  mstep; mstep [Lk]; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep [Lk]
  -- Hook::Custom
  mstep
  mstep; mstep [Hv]; mstep; mstep; mstep
  mstep; mstep [Hd]; mstep
  -- payload.get()
  icases stk_split n _ 4 4 $$ H8 with ⟨H8, H12⟩
  mstep; mstep; mstep; mstep; mstep; mstep [Vg]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 14) (t := 0) (ta := ta) (idx := gidx) (a := ag)
    (type := types[14]!) (inst := inst) (mi := mi) (code := codeG) [.i32 (sp - 32 + 8), .i32 p0])
  isplitr
  · iunfold GetSpec at Sg; iexact Sg
  isplitr
  · iexact FG
  isplitr
  · iexact Hi
  isplitl [Tg]
  · iexact Tg
  isplitr
  · ipureintro; exact ⟨rfl, hta, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [FmtWrite.act2, hAG]; omega
  isplitl [Hg Hlo H8 H12 HG]
  · iframe Hg Hlo HG
    isplitr
    · ipureintro; rfl
    iapply stk_join n _ 4 4
    iframe H8
    iapply stk_addr _ $$ H12; omega
  inext
  iintro %rs Tg Hc HQ
  icases HQ with ⟨%hrs, Hg, Hlo, P8, P12, HG'⟩
  subst hrs
  rw [FmtWrite.act2, hAG]
  mcredits (31 * cfg.regularOpCost + cost474 cfg K bs h + R)
  mstep_post
  -- info.payload := the &dyn Any
  ihave P := (memBytes_append n ((sp - 32).toNat + 8) (bytes32 pp) (bytes32 pv)).2 $$ [P8 P12]
  · isplitl [P8]
    · iexact P8
    iapply memBytes_congr (by simp) |>.1 $$ P12
  ihave I := (memBytes_append n ((sp - 32).toNat + 16) (bytes32 1065704) (bytes32 1065704)).2 $$ [I16 I20]
  · isplitl [I16]
    · iexact I16
    iapply memBytes_congr (by simp) |>.1 $$ I20
  mstep; mstep; mstep [P]; mstep [I]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  icases (memBytes_append n ((sp - 32).toNat + 16) (bytes32 pp) (bytes32 pv)).1 $$ I with ⟨I16, I20⟩
  mstep; mstep; mstep; mstep; mstep
  simp only [UInt32.reduceOfNat]
  mstep [V12]
  -- the hook: 473, then 474, which traps
  iapply mwpi_cons
  iapply (mwpi_call_indirectT' (ty := 14) (t := 0) (ta := ta) (idx := 118) (a := A 473)
    (type := types[14]!) (inst := inst) (mi := mi) (code := f473)
    [.i32 (UInt32.ofNat 1), .i32 (sp - 32 + 16)])
  isplitr
  · iapply (f473_total cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg gt
      (sp - 32) (UInt32.ofNat 1) (sp - 32 + 16) S hS (by omega) (by omega)
      iprop(infoCells n (sp - 32 + 16) pp pv msg loc ∗ G' ∗ D0) K bs hpos hlen hutf h hov)
    iframe F474 Hcode Hts
  isplitr
  · iexact F473
  isplitr
  · iexact Hi
  isplitl [T118]
  · simp only [UInt32.reduceToNat]; iexact T118
  isplitr
  · ipureintro; exact ⟨rfl, hta, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hlo HI HS Hh I16 I20 I24 I28 HG' HD0]
  · isplitr
    · ipureintro; rfl
    iunfold hookPre
    iframe Hg HI HS Hh HG' HD0
    isplitr
    · ipureintro; rfl
    isplitl [Hlo]
    · iapply stk_addr _ $$ Hlo; omega
    iunfold infoCells
    rw [e16]
    iframe I16
    isplitl [I20]
    · iapply memBytes_congr (by simp) |>.1 $$ I20
    isplitl [I24]
    · iapply memBytes_congr (by omega) |>.1 $$ I24
    iapply memBytes_congr (by omega) |>.1 $$ I28
  inext
  isplit
  · iintro %rs - - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT


set_option maxHeartbeats 16000000
open WNear.Binary.PanicFmt
open WNear.Binary.PanicBegin (panicCode')
/-- **What 816 asks of 817**: at the stack pointer `sp`, on `p` holding `(msg, info, loc)` and the
resources `E`, a trap with the host panicked with `bs`, at the cost `K`. -/
def Spec817Total (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (sp p msg info loc : UInt32) (E : IProp GF) (K : Nat) (h : NearState)
    (bs : List UInt8) : IProp GF :=
  MFunSpecT cfg lim d types[0]! inst mi f817 Cg
    (fun args => iprop(⌜args = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ p.toNat ] msg ∗
      n ↦[i32][ p.toNat + 4 ] info ∗ n ↦[i32][ p.toNat + 8 ] loc ∗ E))
    (fun _ => K) (fun _ _ => iprop(False)) (fun _ => failedWith Cg h (expectedError h bs))

instance spec817_total_persistent (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (sp p msg info loc : UInt32) (E : IProp GF) (K : Nat) (h : NearState)
    (bs : List UInt8) : Persistent (Spec817Total cfg lim d inst mi Cg n g gt sp p msg info loc E K h bs) := by
  unfold Spec817Total MFunSpecT; infer_instance


/-- **817 on formatted arguments** (`expect_failed`, `assert_eq!`, …: arguments, or two pieces or
more): the payload `PanicPayload { inner: a, string: None }`; its `get` (826, which formats `a`
into a `String`) is a premise (`GetSpec`, from `Ga` to `G'`). -/
theorem f817_fmt_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (e : Nat)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp p a info loc msg plen alen lpc : UInt32)
    (hb : (plen = 1 ∧ alen ≠ 0) ∨ 2 ≤ plen.toNat) (S : Nat) (hS : 32 ≤ S)
    (hsp : S + 80 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (ha : a.toNat + 24 ≤ 2 ^ 32)
    (hp : p.toNat + 12 ≤ 2 ^ 32) (hinfo : info.toNat + 12 ≤ 2 ^ 32)
    (Ga G' D0 : IProp GF) (Kg K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    code817 e inst mi A n mx ∗ A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗
      GetSpec cfg lim (d + 2) inst mi Cg n g gt (sp - 16 - 32) (sp - 16) (sp - 16 + 4) 1066400 (S + 32) f826
        iprop(fmtPayload n (sp - 16) a ∗ (argsHead n a plen alen ∗ Ga)) G' Kg ∗
      ToStr cfg lim (d + 4) inst mi Cg n g gt (sp - 16 - 32 - 32) (sp - 16 - 32 + 16) S
        iprop(infoCells n (sp - 16 - 32 + 16) (sp - 16 + 4) 1066400 msg loc ∗ G' ∗
          (n ↦[i32][ info.toNat + 8 ] msg ∗ D0)) K bs
      ⊢ Spec817Total cfg lim d inst mi Cg n g gt sp p a info loc
          iprop(stk n (sp.toNat - 80 - S) (S + 80) ∗ n ↦[i32][ info.toNat + 8 ] msg ∗ argsHead n a plen alen ∗
            Ga ∗ envP n ta A lpc 1066360 179 (A 826) D0 h)
          (cost817 cfg f826 Kg K bs h) h bs := by
  iintro ⟨#Hc', #F826, #Sg, #Hts⟩
  iunfold code817 at Hc'
  icases Hc' with ⟨#F883, #F824, #F473, #F474, #Hcode⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 16 - 32).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h16] <;> omega
  have ha824 := hm.funcs 824 (by decide)
  have ha883 := hm.funcs 883 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  iunfold Spec817Total
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, P0, P4, P8, Hs, HM, HA, HGa, HE⟩
  subst hargs
  iunfold argsHead at HA
  icases HA with ⟨A4, A20⟩
  iunfold envP at HE
  icases HE with ⟨HH, Vg, Tg, HD0, HI, HS, Hh⟩
  icases stk_split' n _ (S + 80) (S + 64) 16 (by omega) $$ Hs with ⟨Hlo, Hf⟩
  ihave Hf := stk_addr (show sp.toNat - 80 - S + (S + 64) = (sp - 16).toNat by omega) $$ Hf
  icases stk_split n _ 8 8 $$ Hf with ⟨Hf0, Hf8⟩
  icases stk_split n _ 4 4 $$ Hf0 with ⟨W0, W4⟩
  icases stk4_word n _ $$ W0 with ⟨%w0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%w4, W4⟩
  ihave A20 := memBytes_congr (j := (a + 20).toNat) (by simp [UInt32.toNat_add]; omega) |>.1 $$ A20
  simp only [f817, cost817, cost824]
  generalize hAG : activationGas cfg.regularOpCost (entryLocals f826 [.i32 0, .i32 0]) = AG
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep [P0]; mstep; mstep; mstep; mstep [A20]; mstep
  mstep; mstep; mstep; mstep
  mstep; mstep [A4]
  rcases hb with ⟨h1, hne⟩ | h2
  -- one piece and arguments: to `@3`, then out to `@1`
  on_goal 1 =>
    subst h1
    mstep
    try simp only [UInt32.reduceOfNat]
    mstep
    mstep_taken with (simp [hne])
  -- two pieces or more: the default, `@1`
  on_goal 2 =>
    have hl : ([0, 1] : List Nat)[plen.toNat]?.getD 3 = 3 := by
      rw [List.getElem?_eq_none (by simp; omega)]; rfl
    mstep
    rw [hl]
    mctrl_norm
    mpay
  all_goals
    mcredits (44 * cfg.regularOpCost + (92 * cfg.regularOpCost + AG + Kg + cost474 cfg K bs h) + R)
    mstep; mstep; mstep [W4]
    mstep; mstep; mstep [W0]
    mstep; mstep; mstep; mstep [P4]
    mcall (f883_spec cfg lim (d + 1) types[32]! (by rfl) inst mi n hn Cg info msg) using [HM]
    · iframe HM
    icases HQ with ⟨%hrs, HM⟩
    subst hrs
    mstep; mstep [P8]
    iapply mwpi_cons
    iapply mwpi_callT' (i := 824) (a := A 824) (type := types[45]!) (inst := inst) (mi := mi)
      (code := f824) [.i32 (sp - 16), .i32 1066360, .i32 msg, .i32 loc]
    isplitr
    · iapply (f824_total cfg lim (d + 1) types[45]! inst mi e A n g ta mx hm (by omega) Cg gt
        (sp - 16) (sp - 16) 1066360 msg loc 179 (A 826) f826 (sp - 16 + 4) 1066400 lpc S hS (by omega)
        (by omega) (by decide) iprop(fmtPayload n (sp - 16) a ∗ (argsHead n a _ alen ∗ Ga)) G'
        iprop(n ↦[i32][ info.toNat + 8 ] msg ∗ D0) Kg K bs hpos hlen hutf h hov)
      iframe F826 Sg F473 F474 Hcode Hts
    isplitr
    · iexact F824
    isplitr
    · iexact Hi
    isplitr
    · ipureintro; exact ⟨rfl, ha824, rfl, by omega⟩
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; simp only [cost824]; rw [hAG]; mstep_norm_full; omega
    isplitl [Hg Hlo HH Vg Tg HD0 HI HS Hh W0 W4 Hf8 HGa HM A4 A20]
    · iunfold PanicWithHook.pre
      simp only [UInt32.reduceToNat, Nat.reduceAdd]
      iframe Hg HH Vg Tg HI HS Hh HGa HM HD0
      isplitl [Hlo]
      · iapply stk_addr _ $$ Hlo; omega
      isplitl [W0 W4 Hf8]
      · iunfold fmtPayload
        iframe W0 Hf8
        iapply memBytes_congr (by omega) |>.1 $$ W4
      iunfold argsHead
      iframe A4
      iapply memBytes_congr (by simp [UInt32.toNat_add]; omega) |>.1 $$ A20
    inext
    isplit
    · iintro %rs - HF
      iexfalso
      iexact HF
    · iintro HT
      simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
      iexact HT

/-- `Spec817Total` is antitone in its resources. -/
theorem Spec817Total_mono (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (sp p msg info loc : UInt32) (E E' : IProp GF) (K : Nat) (h : NearState)
    (bs : List UInt8) (hE : E ⊢ E') :
    Spec817Total cfg lim d inst mi Cg n g gt sp p msg info loc E' K h bs ⊢
      Spec817Total cfg lim d inst mi Cg n g gt sp p msg info loc E K h bs := by
  iintro #H
  iunfold Spec817Total, MFunSpecT at H
  iunfold Spec817Total, MFunSpecT
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, P0, P4, P8, HE⟩
  iapply H $$ %args %R [Hg P0 P4 P8 HE] Hc
  beta_reduce
  iframe Hg P0 P4 P8
  isplitr
  · ipureintro; exact hargs
  iapply hE $$ HE

/-! ## `__rust_end_short_backtrace` (816), `rust_begin_unwind` (823), `panic_fmt` (859) -/

/-- **`__rust_end_short_backtrace`** (816) on `p` holding `(msg, info, loc)`: 817 on its copy. -/
theorem f816_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp p msg info loc : UInt32) (hsp : 16 ≤ sp.toNat) (hp : p.toNat + 12 ≤ 2 ^ 32) (E : IProp GF)
    (K : Nat) (h : NearState) (bs : List UInt8) :
    inst ↪[inst] mi ∗ A 817 ↪[wf] FuncInst.wasm types[0]! inst f817 ∗
      Spec817Total cfg lim (d + 1) inst mi Cg n g gt (sp - 16) (sp - 16) msg info loc E K h bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f816 Cg
        (fun args => iprop(⌜args = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ p.toNat ] msg ∗
          n ↦[i32][ p.toNat + 4 ] info ∗ n ↦[i32][ p.toNat + 8 ] loc ∗ stk n (sp.toNat - 16) 16 ∗ E))
        (fun _ => 29 * cfg.regularOpCost + K) (fun _ _ => iprop(False)) (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#Hi, #F817, #S817⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have ha817 := hm.funcs 817 (by decide)
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, P0, P4, P8, Hf, HE⟩
  subst hargs
  ihave Hf := stk_addr (show sp.toNat - 16 = (sp - 16).toNat by omega) $$ Hf
  icases stk_split n _ 8 8 $$ Hf with ⟨Hf0, Hf8⟩
  icases stk_split n _ 4 4 $$ Hf8 with ⟨Hf8, -⟩
  icases stk4_word n _ $$ Hf8 with ⟨%w8, Hf8⟩
  ihave Hf8 := memBytes_congr (j := (sp - 16 + 8).toNat) (by simp [UInt32.toNat_add]; omega) |>.1 $$ Hf8
  iunfold stk at Hf0
  icases Hf0 with ⟨%ob, %hob, Hf0⟩
  ihave PP := (memBytes_append n p.toNat (bytes32 msg) (bytes32 info)).2 $$ [P0 P4]
  · isplitl [P0]
    · iexact P0
    iapply memBytes_congr (by simp) |>.1 $$ P4
  iunfold Spec817Total at S817
  simp only [f816]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [P8]; mstep [Hf8]
  mstep; mstep; mstep [PP]; mstep [Hf0]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  icases (memBytes_append n (sp - 16).toNat (bytes32 msg) (bytes32 info)).1 $$ Hf0 with ⟨Q0, Q4⟩
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 817) (a := A 817) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f817) [.i32 (sp - 16)]
  isplitr
  · iexact S817
  isplitr
  · iexact F817
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha817, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Q0 Q4 Hf8 HE]
  · iframe Hg Q0 HE
    isplitr
    · ipureintro; rfl
    isplitl [Q4]
    · iapply memBytes_congr (by simp) |>.1 $$ Q4
    iapply memBytes_congr (by simp [UInt32.toNat_add]; omega) |>.1 $$ Hf8
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

/-- **`rust_begin_unwind`** (823) on the `PanicInfo` `info` (its message `msg` and location
`loc`, both `Some`): 816 on `(msg, info, loc)`. -/
theorem f823_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp info msg loc : UInt32) (hsp : 32 ≤ sp.toNat) (hinfo : info.toNat + 16 ≤ 2 ^ 32)
    (hmsg : msg ≠ 0) (hloc : loc ≠ 0) (E : IProp GF) (K : Nat) (h : NearState) (bs : List UInt8) :
    inst ↪[inst] mi ∗ A 816 ↪[wf] FuncInst.wasm types[0]! inst f816 ∗
      A 817 ↪[wf] FuncInst.wasm types[0]! inst f817 ∗ A 883 ↪[wf] FuncInst.wasm types[32]! inst f883 ∗
      A 884 ↪[wf] FuncInst.wasm types[32]! inst f884 ∗ A 795 ↪[wf] FuncInst.wasm types[32]! inst f795 ∗
      A 796 ↪[wf] FuncInst.wasm types[13]! inst f796 ∗
      Spec817Total cfg lim (d + 2) inst mi Cg n g gt (sp - 16 - 16) (sp - 16 - 16) msg info loc
        iprop(n ↦[i32][ info.toNat + 8 ] msg ∗ E) K h bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f823 Cg
        (fun args => iprop(⌜args = [.i32 info]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ info.toNat + 8 ] msg ∗
          n ↦[i32][ info.toNat + 12 ] loc ∗ stk n (sp.toNat - 32) 32 ∗ E))
        (fun _ => 109 * cfg.regularOpCost + K) (fun _ _ => iprop(False)) (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#Hi, #F816, #F817, #F883, #F884, #F795, #F796, #S817⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have ha816 := hm.funcs 816 (by decide)
  have ha883 := hm.funcs 883 (by decide)
  have ha884 := hm.funcs 884 (by decide)
  have ha795 := hm.funcs 795 (by decide)
  have ha796 := hm.funcs 796 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, M8, L12, Hs, HE⟩
  subst hargs
  icases stk_split n _ 16 16 $$ Hs with ⟨Hlo, Hf⟩
  ihave Hf := stk_addr (show sp.toNat - 32 + 16 = (sp - 16).toNat by omega) $$ Hf
  icases VecFromElem.stk16 n _ $$ Hf with ⟨W0, W4, W8, -⟩
  icases stk4_word n _ $$ W0 with ⟨%w0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%w4, W4⟩
  icases stk4_word n _ $$ W8 with ⟨%w8, W8⟩
  simp only [f823]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mcall (f884_spec cfg lim (d + 1) types[32]! (by rfl) inst mi n hn Cg info loc) using [L12]
  · iframe L12
  icases HQ with ⟨%hrs, L12⟩
  subst hrs
  mstep
  mcall (f796_some cfg lim (d + 1) types[13]! (by rfl) inst mi Cg loc 1066328 hloc) using []
  · ipureintro; first | trivial | rfl
  icases HQ with %hrs
  subst hrs
  mstep; mstep
  mcall (f883_spec cfg lim (d + 1) types[32]! (by rfl) inst mi n hn Cg info msg) using [M8]
  · iframe M8
  icases HQ with ⟨%hrs, M8⟩
  subst hrs
  mcall (f795_some cfg lim (d + 1) types[32]! (by rfl) inst mi Cg msg hmsg) using []
  · ipureintro; first | trivial | rfl
  icases HQ with %hrs
  subst hrs
  mstep
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep [W4]
  mstep; mstep; mstep [W0]
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 816) (a := A 816) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f816) [.i32 (sp - 16)]
  isplitr
  · iapply (f816_total cfg lim (d + 1) types[0]! inst mi A n g ta hm (by omega) Cg gt (sp - 16) (sp - 16)
      msg info loc (by omega) (by omega) iprop(n ↦[i32][ info.toNat + 8 ] msg ∗ E) K h bs)
    iframe Hi F817 S817
  isplitr
  · iexact F816
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha816, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg W0 W4 W8 Hlo M8 HE]
  · iframe Hg W0 W4 W8 M8 HE
    isplitr
    · ipureintro; rfl
    iapply stk_addr _ $$ Hlo; omega
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

/-- **`core::panicking::panic_fmt(a, loc)`** (859): the `PanicInfo` `(payload (1067136, 1070656),
message a, location loc)` at `sp - 16`, then 823. -/
theorem f859_total (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp a loc : UInt32) (hsp : 48 ≤ sp.toNat) (ha : a ≠ 0) (hloc : loc ≠ 0) (E : IProp GF) (K : Nat)
    (h : NearState) (bs : List UInt8) :
    code859 inst mi A ∗
      Spec817Total cfg lim (d + 3) inst mi Cg n g gt (sp - 16 - 16 - 16) (sp - 16 - 16 - 16) a (sp - 16) loc
        iprop(n ↦[i32][ (sp - 16).toNat + 8 ] a ∗ E) K h bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f859 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 48) 48 ∗ E))
        (fun _ => 138 * cfg.regularOpCost + K) (fun _ _ => iprop(False)) (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#Hc', #S817⟩
  iunfold code859 at Hc'
  icases Hc' with ⟨#Hi, #F823, #F816, #F817, #F883, #F884, #F795, #F796⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have ha823 := hm.funcs 823 (by decide)
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HE⟩
  subst hargs
  icases stk_split n _ 32 16 $$ Hs with ⟨Hlo, Hf⟩
  ihave Hf := stk_addr (show sp.toNat - 48 + 32 = (sp - 16).toNat by omega) $$ Hf
  icases VecFromElem.stk16 n _ $$ Hf with ⟨W0, W4, W8, W12⟩
  icases stk4_word n _ $$ W0 with ⟨%w0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%w4, W4⟩
  icases stk4_word n _ $$ W8 with ⟨%w8, W8⟩
  icases stk4_word n _ $$ W12 with ⟨%w12, W12⟩
  simp only [f859]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [W12]
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep [W4]
  mstep; mstep; mstep [W0]
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 823) (a := A 823) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f823) [.i32 (sp - 16)]
  isplitr
  · iapply (f823_total cfg lim (d + 1) types[0]! inst mi A n g ta hm (by omega) Cg gt (sp - 16) (sp - 16) a
      loc (by omega) (by omega) ha hloc E K h bs)
    iframe Hi F816 F817 F883 F884 F795 F796 S817
  isplitr
  · iexact F823
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha823, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg W8 W12 Hlo HE]
  · iframe Hg W8 W12 HE
    isplitr
    · ipureintro; rfl
    iapply stk_addr _ $$ Hlo; omega
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT


/-! ## The entries: `core::panicking::panic` (853) and `expect_failed` (879) -/

end WNear.Binary.PanicTotal
