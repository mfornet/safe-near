import Bridge.Functions.ScratchGrow

/-! # Scratch operations when capacity is already available -/

namespace WNear.Binary.ScratchFast

open WNear.Binary.ScratchGrow
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeString (heapS costA strCode)
open WNear.Binary.VecGrow (reallocCode reallocated preR postR post154 cost154 growCap growCap_toNat)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Pushing into available capacity skips reserve and costs at most 40 regular operations. -/
theorem f614_fit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec b ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + 1 < 2 ^ 27)
    (hfit : fits cap (UInt32.ofNat bs.length) 1) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f614 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => 40 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) 1⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) 1 ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + 1) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) 1) p
            (capAfter cap (UInt32.ofNat bs.length) 1) (bs ++ [MemSet.byteOf b]))) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, -, -, -, #H589, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha589 := hm.funcs 589 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
  subst hargs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl, hp0, hpc, -⟩, Hsb⟩
  simp only [f614, costApp, costRes, capAfter, fAfter, hlAfter]
  have hfit' := hfit
  simp only [fits, hL, UInt32.toNat_one] at hfit'
  simp only [if_pos hfit]
  have hne : Numeric.bool (Numeric.irelop32 IRelOp.ne (UInt32.ofNat bs.length) cap) = 1 := by
    have : (UInt32.ofNat bs.length) ≠ cap := by
      intro h; have := congrArg UInt32.toNat h; rw [hL] at this; omega
    simp [Numeric.irelop32, Numeric.bool, this]
  repeat mstep
  mstep [Hl]
  mstep; mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hp]
  repeat mstep
  icases sbuf_push (show bs.length < cap.toNat by omega) $$ Hsb with ⟨%j, Hj, Hw⟩
  mstep [Hj] with (simp [UInt32.toNat_add]; omega)
  rw [MemSet.storeBytes_i32_1]
  ispecialize Hw $$ %(MemSet.byteOf b)
  ihave Hsb := Hw $$ Hj
  mstep; mstep; mstep [Hl]
  repeat mstep
  mstep [Hl]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists ptr, hl
  iframe Hg Hs Hvt Hp Hcap Hsb
  isplitr
  · ipureintro; trivial
  have : UInt32.ofNat bs.length + 1 = UInt32.ofNat (bs.length + 1) := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hL]; simp <;> omega
  rw [this]
  iexact Hl


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Fitting `try_reserve` returns without allocating in at most 20 operations. -/
theorem f630_fit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (hs : 96 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hlen : len.toNat = bs.length)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 27) (hfit : fits cap len k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f630 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ out.toNat ] ob))
        (fun _ => 20 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat), ⌜hlAfter hl hl' cap len k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap len k ∗
          n ↦[i32][ out.toNat ] 0 ∗ sbuf n maxP hl' live (fAfter F cap len k) p (capAfter cap len k) bs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, #H631, -, -, -, -, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha631 := hm.funcs 631 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hsb, Ho⟩
  subst hargs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl, -⟩, Hsb⟩
  have hsub : (cap - len).toNat = cap.toNat - len.toNat := by
    rw [UInt32.toNat_sub_of_le]; simp [UInt32.le_iff_toNat_le]; omega
  simp only [f630, costRes, capAfter, fAfter, hlAfter]
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (cap - len) k) = 1 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le, hsub]; omega
  simp only [if_pos hfit]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Ho]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists ptr, hl
  iframe Hg Hs Hvt Hp Hcap Ho Hsb
  ipureintro; trivial


set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Fitting `RawVec::reserve`, including its stack frame and result check. -/
theorem f623_fit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hlen : len.toNat = bs.length)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 27) (hfit : fits cap len k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f623 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => 80 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat), ⌜hlAfter hl hl' cap len k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap len k ∗
          sbuf n maxP hl' live (fAfter F cap len k) p (capAfter cap len k) bs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, #H630, #H628, -, -, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha630 := hm.funcs 630 (by decide)
  have ha628 := hm.funcs 628 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hsb⟩
  subst hargs
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨Lo, Fr⟩
  icases stk_split n (s.toNat - 112 + 96) 4 12 $$ Fr with ⟨O, Fr⟩
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  ihave O := memBytes_addr (show s.toNat - 112 + 96 = (s - 16).toNat by omega) $$ O
  ihave Lo := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ Lo
  have key := f630_fit (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    (s - 16) vec len k ptr cap idx maxP hl live F bs ob (by omega) hob (by omega) hvec hlen hcap2 hlk hfit
  simp only [f623]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall key using [Hg Lo Hvt Hp Hcap Hsb O]
  · iframe Hg Lo Hvt Hp Hcap Hsb O
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, Hp, Hcap, O, Hsb⟩
  subst hrs
  mcredits (40 * cfg.regularOpCost + R)
  repeat mstep
  mcall (f628_ok cfg lim (d + 1) types[0]! rfl inst mi n hn Cg (s - 16)) using [O]
  · iframe O
  icases HQ with ⟨%hrs, O⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists p, hl'
  iframe Hg Hvt Hp Hcap Hsb
  isplitr
  · ipureintro; exact hhl
  ihave O := BorshFT.stkW (b := s.toNat - 112 + 96) 0 (by omega) $$ O
  ihave Lo := stk_addr (show (s - 16).toNat - 96 = s.toNat - 112 by omega) $$ Lo
  ihave Fr := stk_join n (s.toNat - 112 + 96) 4 12 $$ [O Fr]
  · iframe O Fr
  iapply stk_join n (s.toNat - 112) 96 16
  iframe Lo Fr



set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Fitting `Vec::reserve`, at the vector's actual used length. -/
theorem f589_fit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hfit : fits cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f589 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => 100 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) bs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, -, -, #H623, -, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha623 := hm.funcs 623 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have key := f623_fit (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s
    vec (UInt32.ofNat bs.length) k ptr cap idx maxP hl live F bs hs (by omega)
    (by simp; omega) hcap2 (by simp; omega) hfit
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
  subst hargs
  simp only [f589]
  repeat mstep
  mstep [Hl]
  repeat mstep
  mcall key using [Hg Hs Hvt Hp Hcap Hsb]
  · iframe Hg Hs Hvt Hp Hcap Hsb
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hl
  isplitr
  · ipureintro; simp [htype]
  iexists p, hl'
  iframe HQ
  ipureintro; exact hhl



set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Fitting `spec_extend`, including copying all appended bytes. -/
theorem f588_fit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec src k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hsb : sb.length = k.toNat) (hsrc : src.toNat + k.toNat ≤ 2 ^ 32)
    (hfit : fits cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f588 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 src, .i32 (src + k)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ src.toNat ] sb))
        (fun _ => 160 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + k.toNat) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) (bs ++ sb) ∗ n ↦[wms][ src.toNat ] sb)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, #HR, -, -, -, -, -, #H589, -, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -, -, -, -, -, -, #H951, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha589 := hm.funcs 589 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have t15r : types[15]!.results.length = 1 := by rfl
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
  have hsk : src + k - src = k := by rw [UInt32.add_comm]; exact UInt32.add_sub_cancel k src
  have key := f589_fit (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt s
    vec k ptr cap idx maxP hl live F bs hs hvec hcap2 hlk hfit
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  have hM2 : (11 + MemCpy.cost k.toNat) * cfg.regularOpCost = 11 * cfg.regularOpCost + M := by
    rw [Nat.add_mul, hM]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb, Hsrc⟩
  subst hargs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl, -⟩, Hsb⟩
  rw [show 160 * cfg.regularOpCost + M + R = 160 * cfg.regularOpCost + (M + R) by omega]
  simp only [f588]
  repeat mstep
  rw [hsk]
  mcall key using [Hg Hs Hvt Hp Hcap Hl Hsb]
  · iframe Hg Hs Hvt Hp Hcap Hl Hsb
  clear key
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Hs, Hvt, Hp, Hcap, Hl, Hsb⟩
  subst hrs
  icases sbuf_pure $$ Hsb with ⟨%⟨hbl', hp0', hpc', -⟩, Hsb⟩
  have hroom : bs.length + k.toNat ≤ (capAfter cap (UInt32.ofNat bs.length) k).toNat := by
    by_cases h : fits cap (UInt32.ofNat bs.length) k
    · simp only [capAfter, if_pos h]; simp only [fits, hL] at h; omega
    · simp only [capAfter, if_neg h]
      rw [growCap_toNat _ _ (by omega)]
      have : (UInt32.ofNat bs.length + k).toNat = bs.length + k.toNat := by
        rw [UInt32.toNat_add, hL]; omega
      rw [this]; omega
  generalize hca : capAfter cap (UInt32.ofNat bs.length) k = ca at hroom hpc' ⊢
  icases sbuf_app k.toNat hroom $$ Hsb with ⟨%jb, %hjb, Hj, Hw⟩
  mcredits (40 * cfg.regularOpCost + (M + R))
  repeat mstep
  mstep [Hp]
  mstep
  mstep [Hl]
  repeat mstep
  ihave Hj := memBytes_addr (show p.toNat + bs.length = (p + UInt32.ofNat bs.length).toNat by
    rw [UInt32.toNat_add, hL]; omega) $$ Hj
  mcall (MemCpy.f951_spec cfg lim (d + 1) types[15]! t15r inst mi n hn Cg (p + UInt32.ofNat bs.length) src k jb sb
      (by omega) hsb (by rw [UInt32.toNat_add, hL]; omega) hsrc) using [Hj Hsrc]
  · iunfold MemCpy.pre
    iframe Hj Hsrc
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hj, Hsrc⟩
  subst hrs
  try rw [hM2]
  mcredits (10 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Hl]
  repeat mstep
  mstep [Hl]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexists p, hl'
  iframe Hg Hs Hvt Hp Hcap Hsrc
  isplitr
  · ipureintro; exact hhl
  have : UInt32.ofNat bs.length + k = UInt32.ofNat (bs.length + k.toNat) := by
    apply UInt32.toNat_inj.mp; rw [UInt32.toNat_add, hL]; simp <;> omega
  rw [this]
  iframe Hl
  ihave Hj := memBytes_addr (show (p + UInt32.ofNat bs.length).toNat = p.toNat + bs.length by
    rw [UInt32.toNat_add, hL]; omega) $$ Hj
  iapply Hw $$ %sb %hsb Hj



set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Fitting `extend_from_slice` preserves the original append result and all frames. -/
theorem f613_fit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec src k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hsb : sb.length = k.toNat) (hsrc : src.toNat + k.toNat ≤ 2 ^ 32)
    (hfit : fits cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f613 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 src, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ src.toNat ] sb))
        (fun _ => 180 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + k.toNat) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) (bs ++ sb) ∗ n ↦[wms][ src.toNat ] sb)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold sgCode at Hk'
  icases Hk' with ⟨#HS, -, -, -, -, -, -, -, #H588, -, -⟩
  iunfold strCode at HS
  icases HS with ⟨#Hcode, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha588 := hm.funcs 588 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have key := f588_fit (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s
    vec src k ptr cap idx maxP hl live F bs sb hs hvec hcap2 hlk hsb hsrc hfit
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M at key ⊢
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f613]
  repeat mstep
  mcall key using [HP]
  · iframe HP
  clear key
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iexact HQ


/-- Pushing uses the direct branch when possible, retaining the general growth bound otherwise. -/
def pushCost (cfg : WasmConfig) (F : Nat) (cap len : UInt32) : Nat :=
  if fits cap len 1 then 40 * cfg.regularOpCost else costApp cfg F cap len 1

/-- A slice append uses the fitting reserve chain or the existing general growth contract. -/
def extCost (cfg : WasmConfig) (F : Nat) (cap len k : UInt32) : Nat :=
  if fits cap len k then 180 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost
  else 20 * cfg.regularOpCost + costExt cfg F cap len k

/-- The tighter push charge never exceeds the previous bound. -/
theorem pushCost_le (cfg : WasmConfig) (F : Nat) (cap len : UInt32) :
    pushCost cfg F cap len ≤ costApp cfg F cap len 1 := by
  unfold pushCost costApp
  split <;> omega

/-- The original push contract, with a capacity-sensitive cost and the same full result. -/
theorem f614_fast (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec b ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + 1 < 2 ^ 27)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) 1) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f614 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 b]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs))
        (fun _ => pushCost cfg F cap (UInt32.ofNat bs.length))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) 1⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) 1 ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + 1) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) 1) p
            (capAfter cap (UInt32.ofNat bs.length) 1) (bs ++ [MemSet.byteOf b]))) := by
  by_cases hfit : fits cap (UInt32.ofNat bs.length) 1
  · simpa only [pushCost, if_pos hfit] using
      f614_fit (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
        s vec b ptr cap idx maxP hl live F bs hs hvec hcap2 hlk hfit
  · simpa only [pushCost, if_neg hfit] using
      ScratchGrow.f614_spec (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
        s vec b ptr cap idx maxP hl live F bs hs hvec hcap2 hlk hr

/-- The original slice-append contract, with a capacity-sensitive cost and unchanged growth behavior. -/
theorem f613_fast (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec src k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs sb : List UInt8) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hcap2 : cap.toNat < 2 ^ 27) (hlk : bs.length + k.toNat < 2 ^ 27)
    (hsb : sb.length = k.toNat) (hsrc : src.toNat + k.toNat ≤ 2 ^ 32)
    (hr : roomRes hl maxP cap (UInt32.ofNat bs.length) k) :
    sgCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f613 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 src, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗ sbuf n maxP hl live F ptr cap bs ∗
          n ↦[wms][ src.toNat ] sb))
        (fun _ => extCost cfg F cap (UInt32.ofNat bs.length) k)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat),
          ⌜hlAfter hl hl' cap (UInt32.ofNat bs.length) k⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] capAfter cap (UInt32.ofNat bs.length) k ∗
          n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat (bs.length + k.toNat) ∗
          sbuf n maxP hl' live (fAfter F cap (UInt32.ofNat bs.length) k) p
            (capAfter cap (UInt32.ofNat bs.length) k) (bs ++ sb) ∗ n ↦[wms][ src.toNat ] sb)) := by
  by_cases hfit : fits cap (UInt32.ofNat bs.length) k
  · simpa only [extCost, if_pos hfit] using
      f613_fit (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
        s vec src k ptr cap idx maxP hl live F bs sb hs hvec hcap2 hlk hsb hsrc hfit
  · simpa only [extCost, if_neg hfit] using
      ScratchGrow.f613_spec (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
        s vec src k ptr cap idx maxP hl live F bs sb hs hvec hcap2 hlk hsb hsrc hr

end Proof
end WNear.Binary.ScratchFast
