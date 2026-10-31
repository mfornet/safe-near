import Bridge.Functions.PanicTotalCommon
import Bridge.Functions.PanicExpectError

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
open WNear.Binary.PanicFmt
open WNear.Binary.PanicExpectError
/-- Actual unwrap-failure entry consumes the exact total common-panic contract. -/
theorem f881_total_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l err vt loc : UInt32) (hsp : 112 ≤ sp.toNat) (hloc : loc ≠ 0) (E : IProp GF) (K : Nat)
    (h : NearState) (bs : List UInt8) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗
      Spec817Total cfg lim (d + 4) inst mi Cg n g gt (sp - 64 - 16 - 16 - 16) (sp - 64 - 16 - 16 - 16)
        (sp - 64 + 24) (sp - 64 - 16) loc
        iprop(n ↦[i32][ (sp - 64 - 16).toNat + 8 ] (sp - 64 + 24) ∗
          (argsHead n (sp - 64 + 24) 2 2 ∗ expectErrArgs n (sp - 64) m l err vt ∗ E)) K h bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f881 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 err, .i32 vt, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗ E))
        (fun _ => 250 * cfg.regularOpCost + K) (fun _ _ => iprop(False)) (fun _ => failedWith Cg h (expectedError h bs)) := by
  iintro ⟨#Hc', #F859, #S817⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code859 at Hc'
    icases Hc' with ⟨#Hi, -⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e24 : (sp - 64 + 24).toNat = (sp - 64).toNat + 24 := by simp [UInt32.toNat_add]; omega
  have hne : sp - 64 + 24 ≠ 0 := by
    intro e; have := congrArg UInt32.toNat e; simp only [e24, UInt32.reduceToNat] at this; omega
  have ha859 := hm.funcs 859 (by decide)
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HE⟩
  subst hargs
  icases stk_split n _ 48 64 $$ Hs with ⟨Hlo, Hf⟩
  ihave Hf := stk_addr (show sp.toNat - 112 + 48 = (sp - 64).toNat by omega) $$ Hf
  icases stk_split n _ 16 48 $$ Hf with ⟨H0, Hf⟩
  icases stk_split n _ 16 32 $$ Hf with ⟨H16, Hf⟩
  icases stk_split n _ 16 16 $$ Hf with ⟨H32, H48⟩
  icases VecFromElem.stk16 n _ $$ H0 with ⟨-, -, W8, W12⟩
  icases VecFromElem.stk16 n _ $$ H16 with ⟨W16, W20, W24, W28⟩
  icases VecFromElem.stk16 n _ $$ H32 with ⟨W32, -, W40, W44⟩
  icases VecFromElem.stk16 n _ $$ H48 with ⟨W48, W52, W56, W60⟩
  icases stk4_word n _ $$ W8 with ⟨%w8, W8⟩
  ihave W8 := memBytes_congr (j := (sp - 64).toNat + 8) (by omega) |>.1 $$ W8
  icases stk4_word n _ $$ W12 with ⟨%w12, W12⟩
  ihave W12 := memBytes_congr (j := (sp - 64).toNat + 12) (by omega) |>.1 $$ W12
  icases stk4_word n _ $$ W16 with ⟨%w16, W16⟩
  ihave W16 := memBytes_congr (j := (sp - 64).toNat + 16) (by omega) |>.1 $$ W16
  icases stk4_word n _ $$ W20 with ⟨%w20, W20⟩
  ihave W20 := memBytes_congr (j := (sp - 64).toNat + 20) (by omega) |>.1 $$ W20
  icases stk4_word n _ $$ W24 with ⟨%w24, W24⟩
  ihave W24 := memBytes_congr (j := (sp - 64).toNat + 24) (by omega) |>.1 $$ W24
  icases stk4_word n _ $$ W28 with ⟨%w28, W28⟩
  ihave W28 := memBytes_congr (j := (sp - 64).toNat + 28) (by omega) |>.1 $$ W28
  icases stk4_word n _ $$ W32 with ⟨%w32, W32⟩
  ihave W32 := memBytes_congr (j := (sp - 64).toNat + 32) (by omega) |>.1 $$ W32
  icases stk4_word n _ $$ W40 with ⟨%w40, W40⟩
  ihave W40 := memBytes_congr (j := (sp - 64).toNat + 40) (by omega) |>.1 $$ W40
  icases stk4_word n _ $$ W44 with ⟨%w44, W44⟩
  ihave W44 := memBytes_congr (j := (sp - 64).toNat + 44) (by omega) |>.1 $$ W44
  icases stk4_word n _ $$ W48 with ⟨%w48, W48⟩
  ihave W48 := memBytes_congr (j := (sp - 64).toNat + 48) (by omega) |>.1 $$ W48
  icases stk4_word n _ $$ W52 with ⟨%w52, W52⟩
  ihave W52 := memBytes_congr (j := (sp - 64).toNat + 52) (by omega) |>.1 $$ W52
  icases stk4_word n _ $$ W56 with ⟨%w56, W56⟩
  ihave W56 := memBytes_congr (j := (sp - 64).toNat + 56) (by omega) |>.1 $$ W56
  icases stk4_word n _ $$ W60 with ⟨%w60, W60⟩
  ihave W60 := memBytes_congr (j := (sp - 64).toNat + 60) (by omega) |>.1 $$ W60
  ihave W28 := BorshFT.join64' (n := n) (a := (sp - 64).toNat + 28) (b := (sp - 64).toNat + 32)
    w28 w32 (by omega) $$ [W28 W32]
  · iframe W28 W32
  ihave W44 := memBytes_congr (j := (sp - 64 + 44).toNat) (by simp [UInt32.toNat_add]; omega) |>.1 $$ W44
  ihave W60 := memBytes_congr (j := (sp - 64 + 60).toNat) (by simp [UInt32.toNat_add]; omega) |>.1 $$ W60
  simp only [f881]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [W12]
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep [W20]
  mstep; mstep; mstep [W16]
  mstep; mstep; mstep; mstep; mstep [W44]
  mstep; mstep; mstep; mstep; mstep [W60]
  mstep; mstep; mstep [W28]
  mstep; mstep; mstep [W24]
  mstep; mstep; mstep [W52]
  mstep; mstep; mstep; mstep; mstep [W40]
  mstep; mstep; mstep; mstep; mstep [W56]
  mstep; mstep; mstep; mstep; mstep [W48]
  mstep; mstep; mstep; mstep
  rw [show storeBytes (.i64 2) 8 = bytes32 2 ++ bytes32 0 by decide]
  icases (memBytes_append n ((sp - 64).toNat + 28) (bytes32 2) (bytes32 0)).1 $$ W28 with ⟨W28, W32⟩
  iapply mwpi_cons
  iapply mwpi_callT' (i := 859) (a := A 859) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f859) [.i32 (sp - 64 + 24), .i32 loc]
  isplitr
  · iapply (f859_total cfg lim (d + 1) types[14]! inst mi A n g ta hm (by omega) Cg gt (sp - 64)
      (sp - 64 + 24) loc (by omega) hne hloc
      iprop(argsHead n (sp - 64 + 24) 2 2 ∗ expectErrArgs n (sp - 64) m l err vt ∗ E) K h bs)
    iframe Hc' S817
  isplitr
  · iexact F859
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha859, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hlo HE W8 W12 W16 W20 W24 W28 W32 W40 W44 W48 W52 W56 W60]
  · iframe Hg HE
    isplitr
    · ipureintro; rfl
    isplitl [Hlo]
    · iapply stk_addr _ $$ Hlo; omega
    ihave W28 := memBytes_congr (j := (sp - 64 + 24).toNat + 4) (by omega) |>.1 $$ W28
    ihave W44 := memBytes_congr (j := (sp - 64 + 24).toNat + 20) (by simp [UInt32.toNat_add]; omega) |>.1 $$ W44
    ihave W32 := memBytes_congr (j := (sp - 64).toNat + 32) (by simp [bytes32_length]) |>.1 $$ W32
    ihave W60 := memBytes_congr (j := (sp - 64).toNat + 60) (by simp [UInt32.toNat_add]; omega) |>.1 $$ W60
    iunfold argsHead, expectErrArgs
    iframe W8 W12 W16 W20 W24 W28 W32 W40 W44 W48 W52 W56 W60
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

/-- Actual unwrap-failure entry constructs both panic message-size branches from Get and ToStr. -/
theorem f881_total_full (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l err vt loc lpc : UInt32) (hloc : loc ≠ 0) (S : Nat) (hS : 32 ≤ S) (hsp : S + 192 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (Ga G' D1 : IProp GF) (Kg K : Nat) (bs : List UInt8)
    (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗
      GetSpec cfg lim (d + 6) inst mi Cg n g gt (sp - 64 - 16 - 16 - 16 - 16 - 32) (sp - 64 - 16 - 16 - 16 - 16)
        (sp - 64 - 16 - 16 - 16 - 16 + 4) 1066400 (S + 32) f826
        iprop(fmtPayload n (sp - 64 - 16 - 16 - 16 - 16) (sp - 64 + 24) ∗
          (argsHead n (sp - 64 + 24) 2 2 ∗ (expectErrArgs n (sp - 64) m l err vt ∗ Ga))) G' Kg ∗
      ToStr cfg lim (d + 8) inst mi Cg n g gt (sp - 64 - 16 - 16 - 16 - 16 - 32 - 32)
        (sp - 64 - 16 - 16 - 16 - 16 - 32 + 16) S
        iprop(infoCells n (sp - 64 - 16 - 16 - 16 - 16 - 32 + 16) (sp - 64 - 16 - 16 - 16 - 16 + 4) 1066400
            (sp - 64 + 24) loc ∗ G' ∗
          (n ↦[i32][ (sp - 64 - 16).toNat + 8 ] (sp - 64 + 24) ∗ D1)) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f881 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 err, .i32 vt, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112) 112 ∗
          (stk n ((sp - 64 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗
            envP n ta A lpc 1066360 179 (A 826) D1 h)))
        (fun _ => 250 * cfg.regularOpCost + cost817 cfg f826 Kg K bs h) (fun _ _ => iprop(False))
        (fun _ => failedWith Cg h (expectedError h bs)) := by
  have hlt := sp.toNat_lt
  have h48 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h64 : (sp - 64 - 16).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h80 : (sp - 64 - 16 - 16).toNat = sp.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  have h96 : (sp - 64 - 16 - 16 - 16).toNat = sp.toNat - 112 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have e16 : (sp - 64 + 24).toNat = (sp - 64).toNat + 24 := by simp [UInt32.toNat_add]; omega
  iintro ⟨#H859, #F859, #H817, #F826, #Sg, #Hts⟩
  ihave #S817 := f817_fmt_total cfg lim (d + 4) inst mi e A n g ta mx hm (by omega) Cg gt
    (sp - 64 - 16 - 16 - 16) (sp - 64 - 16 - 16 - 16) (sp - 64 + 24) (sp - 64 - 16) loc (sp - 64 + 24) 2 2
    lpc (Or.inr (by decide)) S hS (by omega) (by omega) (by omega) (by omega) (by omega)
    iprop(expectErrArgs n (sp - 64) m l err vt ∗ Ga) G' D1 Kg K bs hpos hlen hutf h hov $$ [H817 F826 Sg Hts]
  · iframe H817 F826 Sg Hts
  ihave #S817' := Spec817Total_mono cfg lim (d + 4) inst mi Cg n g gt (sp - 64 - 16 - 16 - 16)
    (sp - 64 - 16 - 16 - 16) (sp - 64 + 24) (sp - 64 - 16) loc
    iprop(n ↦[i32][ (sp - 64 - 16).toNat + 8 ] (sp - 64 + 24) ∗
      (argsHead n (sp - 64 + 24) 2 2 ∗ expectErrArgs n (sp - 64) m l err vt ∗
        (stk n ((sp - 64 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗
          envP n ta A lpc 1066360 179 (A 826) D1 h)))
    _ _ h bs (by
      iintro ⟨I8, HA, EA, Hs, HGa, HE⟩
      iframe I8 HA Hs HGa EA HE) $$ S817
  iapply (f881_total_spec cfg lim d type inst mi A n g ta hm (by omega) Cg gt sp m l err vt loc (by omega) hloc
    iprop(stk n ((sp - 64 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗
      envP n ta A lpc 1066360 179 (A 826) D1 h) (cost817 cfg f826 Kg K bs h) h bs)
  iframe H859 F859 S817'

end WNear.Binary.PanicTotal
