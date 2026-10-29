import Bridge.Functions.ParseEscape
import Bridge.Functions.SerdeEscSuccess

/-! # Successful escapes without a whole-input error reserve -/

namespace WNear.Binary.ParseEscapeSuccess

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.ParseEscape
open WNear.Binary.EncodeUtf8 (enc605 enc605_eq)
open NearInterface.Json (hex4 unicodeEscape)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeErrBox (errCode roomFor4)
open WNear.Binary.SerdeEsc (eofCode okPack hexTable)
open WNear.Binary.ScratchGrow (sbuf sgCode capAfter fAfter hlAfter roomRes costExt costApp)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option hygiene false in
/-- A simple escape: `push(scratch, v)` (614), then `Ok`. `hd` gives the model's decoding. -/
local macro "push649 " v:term:max : tactic => `(tactic| (
  have hK1 : escK (bs.drop j) = 1 := by simp [escK, hd]
  rw [hK1] at hX hr
  unfold costExt at hX
  generalize hK2 : costApp cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat 1) = K2 at hX
  subst hL
  ihave Hsb := sbuf_join $$ [Hinv Hw]
  · iframe Hinv Hw
  ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
  ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
  · iframe L16 Lo
  have key := ScratchGrow.f614_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) sc $v ptrS capS idx maxP hl live F acc (by omega) (by omega) hcap (by omega) hr
  rw [show UInt32.ofNat 1 = (1 : UInt32) from rfl] at hK2
  rw [hK2] at key
  ihave #S614 := key $$ HG
  rw [show X + R = K2 + ((X - K2) + R) by omega]
  repeat mstep
  mcall S614 using [Hg Lo Hvt S0 S4 S8 Hsb]
  · iframe Hg Lo Hvt S0 S4 S8 Hsb
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, S0, S4, S8, Hsb⟩
  subst hrs
  mcredits (50 * cfg.regularOpCost + ((X - K2) + R))
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Ht
  simp only [res649, hd, htype, Nat.sub_self, List.drop_zero, List.length_singleton]
  rw [show MemSet.byteOf $v = ($v : UInt8) from rfl]
  rw [show UInt32.ofNat 1 = (1 : UInt32) from rfl]
  isplitr [Hrd S0 S4 S8 Hsb]
  · ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
    iapply stk_join n (s.toNat - 144) 112 32
    iframe Lo Fr
  iframe Hrd
  iexists p, hl'
  iframe S0 S4 S8 Hsb
  ipureintro; exact hhl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- 649 when the escape is not `\u`. -/
theorem f649_nu_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hvalid : (escDecode (bs.drop j)).isSome = true)
    (hnu : ∀ rest, bs.drop j ≠ 0x75 :: rest)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => 400 * cfg.regularOpCost +
          costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold escCode at Hk'
  icases Hk' with ⟨#HG, #HE, #H651, #H605, -⟩
  ihave #HE' := HE
  iunfold eofCode at HE'
  icases HE' with ⟨#HErr, #H637, -, -, #H655, #H653⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #H613, #H614⟩
  ihave #HErr' := HErr
  iunfold errCode at HErr'
  icases HErr' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have ha651 := hm.funcs 651 (by decide)
  have ha614 := hm.funcs 614 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha605 := hm.funcs 605 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hrd, S0, S4, S8, Hsb, Ht⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
  generalize hX : costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))) = X
  icases sbuf_split $$ Hsb with ⟨Hinv, Hw⟩
  generalize hL : (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) = L
  simp only [f649]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  icases stk_split n ((s - 32).toNat - 112) 16 96 $$ Lo with ⟨L16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 112 + 16 = (s - 32).toNat - 96 by omega) $$ Lo
  have hjl : j < bs.length := by
    by_contra h
    have hnone : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    simp [hnone, escDecode] at hvalid
  mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
    hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 32) de ptr bs j hjl (by omega) hptr hde)
    using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  have hb := okPack_bit de bs[j]
  mcredits (200 * cfg.regularOpCost + (X + R))
  mstep; mstep; mstep; mstep; mstep
  iterate 11 mstep
  iterate 6 mstep
  rw [okPack_byte]
  obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
  have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
  rw [hx]
  mstep; mstep; mstep
  by_cases hn : x = 110
  · subst hn
    have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((110 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 7 := by
      rw [tab1]; decide
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have hd : escDecode (bs.drop j) = some ([10], 1) := by rw [hdrop]; simp [escDecode]
    push649 10
  by_cases hr1 : x = 114
  · subst hr1
    have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((114 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 8 := by
      rw [tab1]; decide
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have hd : escDecode (bs.drop j) = some ([13], 1) := by rw [hdrop]; simp [escDecode]
    push649 13
  by_cases ht1 : x = 116
  · subst ht1
    have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((116 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 9 := by
      rw [tab1]; decide
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have hd : escDecode (bs.drop j) = some ([9], 1) := by rw [hdrop]; simp [escDecode]
    push649 9
  by_cases hu1 : x = 117
  · exfalso; exact hnu _ (by rw [hdrop, hu1])
  by_cases he1 : x = 111 ∨ x = 112 ∨ x = 113 ∨ x = 115
  · have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[(x.toUInt32 + 4294967186).toNat]?.getD 0 = 1 := by
      rw [tab1, if_neg hn, if_neg hr1, if_neg ht1, if_neg hu1, if_pos he1]
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have hd : escDecode (bs.drop j) = none := by
      rw [hdrop]; rcases he1 with h | h | h | h <;> subst h <;> simp [escDecode]
    exfalso; simpa [hd] using hvalid
  · have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[(x.toUInt32 + 4294967186).toNat]?.getD 0 = 0 := by
      rw [tab1, if_neg hn, if_neg hr1, if_neg ht1, if_neg hu1, if_neg he1]
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    mstep; mstep; mstep; mstep
    by_cases hb1 : x = 98
    · subst hb1
      have hk : ([5, 1, 1, 1, 6] : List Nat)[((98 : UInt8).toUInt32 + 4294967198).toNat]?.getD 0 = 5 := by
        rw [tab2]; decide
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = some ([8], 1) := by rw [hdrop]; simp [escDecode]
      push649 8
    by_cases hf1 : x = 102
    · subst hf1
      have hk : ([5, 1, 1, 1, 6] : List Nat)[((102 : UInt8).toUInt32 + 4294967198).toNat]?.getD 0 = 6 := by
        rw [tab2]; decide
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = some ([12], 1) := by rw [hdrop]; simp [escDecode]
      push649 12
    by_cases he2 : x = 99 ∨ x = 100 ∨ x = 101
    · have hk : ([5, 1, 1, 1, 6] : List Nat)[(x.toUInt32 + 4294967198).toNat]?.getD 0 = 1 := by
        rw [tab2, if_neg hb1, if_neg hf1, if_pos he2]
      iapply FromUtf8Gen.mwpi_br_table_k hk
      isplitr
      · ipureintro; rfl
      clear hk
      mctrl_norm; repeat mpay
      have hd : escDecode (bs.drop j) = none := by
        rw [hdrop]; rcases he2 with h | h | h <;> subst h <;> simp [escDecode]
      exfalso; simpa [hd] using hvalid
    have hk : ([5, 1, 1, 1, 6] : List Nat)[(x.toUInt32 + 4294967198).toNat]?.getD 0 = 0 := by
      rw [tab2, if_neg hb1, if_neg hf1, if_neg he2]
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    by_cases hq : x = 34
    · subst hq
      have h1 : Numeric.bool (Numeric.irelop32 IRelOp.eq (34 : UInt8).toUInt32 34) = 1 := by decide
      repeat mstep
      have hd : escDecode (bs.drop j) = some ([34], 1) := by rw [hdrop]; simp [escDecode]
      push649 34
    have h1 := u8_ne x 34 hq
    by_cases hsl : x = 47
    · subst hsl
      have h2 : Numeric.bool (Numeric.irelop32 IRelOp.eq (47 : UInt8).toUInt32 47) = 1 := by decide
      repeat mstep
      have hd : escDecode (bs.drop j) = some ([47], 1) := by rw [hdrop]; simp [escDecode]
      push649 47
    have h2 := u8_ne x 47 hsl
    by_cases hbs : x = 92
    · subst hbs
      have h3 : Numeric.bool (Numeric.irelop32 IRelOp.eq (92 : UInt8).toUInt32 92) = 1 := by decide
      repeat mstep
      have hd : escDecode (bs.drop j) = some ([92], 1) := by rw [hdrop]; simp [escDecode]
      push649 92
    have h3 := u8_ne x 92 hbs
    repeat mstep
    have hd : escDecode (bs.drop j) = none := by
      rw [hdrop]; simp [escDecode, hq, hsl, hbs, hb1, hf1, hn, hr1, ht1, hu1]
    exfalso; simpa [hd] using hvalid

set_option hygiene false in
/-- The decoded code point `cp` (in local 4) encoded (605) and appended (613), then `Ok`. Needs `hcp : cp <
0x110000`, `hd : escDecode (bs.drop j) = some (enc605 cp, _)` and the reader at `jr`. -/
local macro "enc649 " cp:term:max jr:term:max ep:term:max : tactic => `(tactic| (
  have hK1 : escK (bs.drop j) = (enc605 $cp).length := by simp [escK, hd]
  rw [hK1] at hX hr
  have hkl := EncodeUtf8.enc605_length $cp
  have hk4 : (enc605 $cp).length ≤ 4 := by rw [hkl]; split_ifs <;> omega
  icases stk_split n (s.toNat - 144 + 112) 8 24 $$ Fr with ⟨F0, F1⟩
  icases stk_split n (s.toNat - 144 + 112 + 8) 8 16 $$ F1 with ⟨OB, F2⟩
  icases stk_split n (s.toNat - 144 + 112 + 8 + 8) 4 12 $$ F2 with ⟨BF, F4⟩
  iunfold stk at OB BF
  icases OB with ⟨%ob, %hob, OB⟩
  icases BF with ⟨%bf, %hbf, BF⟩
  ihave BF := memBytes_addr (show s.toNat - 144 + 112 + 8 + 8 = (s - 32).toNat + 16 by omega) $$ BF
  mstep [BF]
  repeat mstep
  ihave OB := memBytes_addr (show s.toNat - 144 + 112 + 8 = (s - 32 + 8).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ OB
  ihave BF := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ BF
  mcall (EncodeUtf8.f605_spec cfg lim (d + 1) types[31]! rfl inst mi n hm.mem Cg (s - 32 + 8) (UInt32.ofNat $cp)
      (s - 32 + 16) ob (bytes32 0) hob (by simp [bytes32]) (by simp; omega)
      (by rw [UInt32.toNat_add, h32]; simp; omega) (by rw [UInt32.toNat_add, h32]; simp; omega)) using [OB BF]
  · iframe OB BF
  icases HQ with ⟨%hrs, O0, O4, BF⟩
  subst hrs
  rw [show (UInt32.ofNat $cp).toNat = $cp by simp; omega]
  ihave O0 := memBytes_addr (show (s - 32 + 8).toNat = (s - 32).toNat + 8 by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ O0
  ihave O4 := memBytes_addr (show (s - 32 + 8).toNat + 4 = (s - 32).toNat + 12 by
    rw [UInt32.toNat_add, h32]; simp; omega) $$ O4
  mstep; mstep; mstep [O0]; mstep; mstep [O4]
  icases U128From.memBytes_split n (s - 32 + 16).toNat (enc605 $cp).length _ (by simp) $$ BF with ⟨B1, B2⟩
  rw [List.take_left' rfl]
  subst hL
  ihave Hsb := sbuf_join $$ [Hinv Hw]
  · iframe Hinv Hw
  ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
  ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
  · iframe L16 Lo
  have hkn : (UInt32.ofNat (enc605 $cp).length).toNat = (enc605 $cp).length := by simp; omega
  have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) sc (s - 32 + 16) (UInt32.ofNat (enc605 $cp).length) ptrS capS idx maxP hl live F acc (enc605 $cp)
    (by omega) (by omega) hcap (by omega) hkn.symm (by rw [UInt32.toNat_add, h32, hkn]; simp; omega) hr
  rw [hX] at key
  ihave #S613 := key $$ HG
  mcredits (100 * cfg.regularOpCost + ($ep + X + R))
  rw [show $ep + X + R = X + ($ep + R) by omega]
  mcall S613 using [Hg Lo Hvt S0 S4 S8 Hsb B1]
  · iframe Hg Lo Hvt S0 S4 S8 Hsb B1
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, S0, S4, S8, Hsb, B1⟩
  subst hrs
  mcredits (30 * cfg.regularOpCost + ($ep + R))
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Ht
  simp only [res649, hd, htype, Nat.sub_self, List.drop_zero]
  rw [show j + ($jr - j) = $jr by omega, hkn]
  isplitr [Hrd S0 S4 S8 Hsb]
  · ihave Lo := stk_addr (show (s - 32).toNat - 112 = s.toNat - 144 by omega) $$ Lo
    ihave O0 := BorshFT.stkW (b := s.toNat - 144 + 112 + 8) _ (by omega) $$ O0
    ihave O4 := BorshFT.stkW (b := s.toNat - 144 + 112 + 8 + 4) _ (by omega) $$ O4
    ihave OB := stk_join n (s.toNat - 144 + 112 + 8) 4 4 $$ [O0 O4]
    · iframe O0 O4
    ihave B := U128From.memBytes_join n (s - 32 + 16).toNat (enc605 $cp).length _ _ rfl $$ [B1 B2]
    · iframe B1 B2
    ihave B := BorshFT.stkB (b := s.toNat - 144 + 112 + 8 + 8) (k := 4) _ (by rw [UInt32.toNat_add, h32]; simp; omega)
      (by simp [bytes32]; omega) $$ B
    ihave F2 := stk_join n (s.toNat - 144 + 112 + 8 + 8) 4 12 $$ [B F4]
    · iframe B F4
    ihave F1 := stk_join n (s.toNat - 144 + 112 + 8) 8 16 $$ [OB F2]
    · iframe OB F2
    ihave Fr := stk_join n (s.toNat - 144 + 112) 8 24 $$ [F0 F1]
    · iframe F0 F1
    iapply stk_join n (s.toNat - 144) 112 32
    iframe Lo Fr
  iframe Hrd
  iexists p, hl'
  iframe S0 S4 S8 Hsb
  ipureintro; exact hhl))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- 649 on `\u` with four hex digits that are not a high surrogate, or no four hex digits. -/
theorem f649_u0_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hvalid : (escDecode (bs.drop j)).isSome = true)
    (hu : ∃ rest, bs.drop j = 0x75 :: rest) (hlo : ∀ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) → nv / 1024 ≠ 54)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => 900 * cfg.regularOpCost +
          costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold escCode at Hk'
  icases Hk' with ⟨#HG, #HE, #H651, #H605, -⟩
  ihave #HE' := HE
  iunfold eofCode at HE'
  icases HE' with ⟨#HErr, #H637, -, -, #H655, #H653⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #H613, #H614⟩
  ihave #HErr' := HErr
  iunfold errCode at HErr'
  icases HErr' with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha655 := hm.funcs 655 (by decide)
  have ha653 := hm.funcs 653 (by decide)
  have ha651 := hm.funcs 651 (by decide)
  have ha614 := hm.funcs 614 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha605 := hm.funcs 605 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hrd, S0, S4, S8, Hsb, Ht⟩
  subst hargs
  icases stk_split n (s.toNat - 144) 112 32 $$ Hs with ⟨Lo, Fr⟩
  ihave Lo := stk_addr (show s.toNat - 144 = (s - 32).toNat - 112 by omega) $$ Lo
  generalize hX : costExt cfg F capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j))) = X
  icases sbuf_split $$ Hsb with ⟨Hinv, Hw⟩
  generalize hL : (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) = L
  simp only [f649]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  icases stk_split n ((s - 32).toNat - 112) 16 96 $$ Lo with ⟨L16, Lo⟩
  ihave Lo := stk_addr (show (s - 32).toNat - 112 + 16 = (s - 32).toNat - 96 by omega) $$ Lo
  have hjl : j < bs.length := by
    by_contra h
    have hnone : bs.drop j = [] := List.drop_eq_nil_of_le (by omega)
    simp [hnone, escDecode] at hvalid
  mcall (SerdeEscSuccess.f655_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi n g (A 637)
    hn hg (hm.funcs 637 (by decide)) (by omega) Cg gt (s - 32) de ptr bs j hjl (by omega) hptr hde)
    using [Hg Hrd]
  · iframe Hg Hrd
  icases HQ with ⟨%hrs, Hg, Hrd⟩
  subst hrs
  have hb := okPack_bit de bs[j]
  mcredits (700 * cfg.regularOpCost + (X + R))
  mstep; mstep; mstep; mstep; mstep
  iterate 11 mstep
  iterate 6 mstep
  rw [okPack_byte]
  obtain ⟨x, hx⟩ : ∃ x, bs[j] = x := ⟨_, rfl⟩
  have hdrop : bs.drop j = x :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hjl, hx]
  rw [hx]
  mstep; mstep; mstep
  have hx117 : x = 117 := by obtain ⟨r, hr⟩ := hu; rw [hdrop] at hr; simp at hr; exact hr.1
  subst hx117
  have hk : ([7, 1, 1, 1, 8, 1, 9, 10] : List Nat)[((117 : UInt8).toUInt32 + 4294967186).toNat]?.getD 0 = 10 := by
    rw [tab1]; decide
  iapply FromUtf8Gen.mwpi_br_table_k hk
  isplitr
  · ipureintro; rfl
  clear hk
  mctrl_norm; repeat mpay
  have hhValid : (hex4 (bs.drop (j + 1))).isSome = true := by
    cases hh : hex4 (bs.drop (j + 1)) with
    | none =>
      have hd : escDecode (bs.drop j) = none := by rw [hdrop]; simp [escDecode, unicodeEscape, hh]
      simpa [hd] using hvalid
    | some pr => rfl
  have key := SerdeEscSuccess.f653_some (GF := GF) cfg lim (d + 1) types[11]! rfl inst mi A n g ta hm
    (by omega) Cg gt (s - 32) de ptr idx bs (j + 1) maxP hl L F hde (by omega) (by omega) hptr (by omega) hhValid
  ihave #S653 := key $$ HE
  repeat mstep
  mcall S653 using [Hg Lo Hvt Hinv Hrd Ht]
  · iframe Hg Lo Hvt Hinv Hrd Ht
  icases HQ with ⟨Hg, Lo, Hvt, Ht, HQ⟩
  mcredits (350 * cfg.regularOpCost + (X + R))
  cases hh : hex4 (bs.drop (j + 1)) with
  | none => exfalso; simpa [hh] using hhValid
  | some pr =>
    obtain ⟨nv, r1⟩ := pr
    simp only [SerdeEsc.res653, hh]
    icases HQ with ⟨%hrs, Hinv, Hrd⟩
    subst hrs
    have hh' := hh
    rw [SerdeEsc.hex4_eq] at hh'
    split at hh'
    case isFalse => simp at hh'
    rename_i h4
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hh'
    obtain ⟨nv', hacc4, rfl, rfl⟩ := hh'
    have hnv := SerdeEsc.hexAcc_lt _ _ hacc4
    have h4' : 4 ≤ bs.length - (j + 1) := by simpa using h4
    simp only [List.length_take, List.length_drop, show min 4 (bs.length - (j + 1)) = 4 by omega] at hnv
    have hnv' : nv' < 65536 := by simpa using hnv
    have hb := hexPack_low nv' hnv'
    repeat mstep
    rw [hexPack_val nv' hnv']
    repeat mstep
    rw [mask10 nv' hnv']
    repeat mstep
    rw [eqc _ _ (by omega)]
    by_cases hhi : nv' / 1024 = 54
    · exfalso; exact hlo _ _ hh hhi
    rw [if_neg (by intro h; apply hhi; have : (55296 : UInt32).toNat = 55296 := rfl; omega)]
    repeat mstep
    rw [eqc _ _ (by omega)]
    by_cases hlo : nv' / 1024 = 55
    · rw [if_pos (by rw [hlo]; rfl)]
      have hd : escDecode (bs.drop j) = none := by
        rw [hdrop]; simp [escDecode, ue_lo _ _ _ hh (by omega)]
      exfalso; simpa [hd] using hvalid
    rw [if_neg (by intro h; apply hlo; have : (56320 : UInt32).toNat = 56320 := rfl; omega)]
    repeat mstep
    rw [mask11 nv' hnv', eqc _ _ (by omega),
      if_neg (by intro h; have : (55296 : UInt32).toNat = 55296 := rfl; omega)]
    repeat mstep
    rw [show UInt32.ofNat nv' &&& 65535 = UInt32.ofNat nv' by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_and, show (65535 : UInt32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      simp; omega]
    have hcp : nv' < 0x110000 := by omega
    have hd : escDecode (bs.drop j) = some (enc605 nv', (j + 1 + 4) - j) := by
      rw [hdrop]
      simp only [escDecode, show (117 : UInt8) ≠ 0x22 by decide, show (117 : UInt8) ≠ 0x5C by decide,
        show (117 : UInt8) ≠ 0x2F by decide, show (117 : UInt8) ≠ 0x62 by decide,
        show (117 : UInt8) ≠ 0x66 by decide, show (117 : UInt8) ≠ 0x6E by decide,
        show (117 : UInt8) ≠ 0x72 by decide, show (117 : UInt8) ≠ 0x74 by decide, ite_false, ite_true]
      rw [ue_bmp _ _ _ hh (by omega)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨(enc605_eq _ (by simp [Nat.isValidChar]; omega)).symm, ?_⟩
      simp; omega
    enc649 nv' (j + 1 + 4) 0

end Proof
end WNear.Binary.ParseEscapeSuccess
