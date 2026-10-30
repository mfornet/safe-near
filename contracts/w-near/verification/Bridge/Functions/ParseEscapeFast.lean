import Bridge.Functions.ParseEscapeSuccessCost
import Bridge.Functions.ScratchFast

/-! # Tighter successful escape costs using the direct push branch -/

namespace WNear.Binary.ParseEscapeFast

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
  rw [hK1] at hr
  subst hL
  ihave Hsb := sbuf_join $$ [Hinv Hw]
  · iframe Hinv Hw
  ihave Lo := stk_addr (show (s - 32).toNat - 96 = (s - 32).toNat - 112 + 16 by omega) $$ Lo
  ihave Lo := stk_join n ((s - 32).toNat - 112) 16 96 $$ [L16 Lo]
  · iframe L16 Lo
  have key := ScratchFast.f614_fast (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega) Cg gt
    (s - 32) sc $v ptrS capS idx maxP hl live F acc (by omega) (by omega) hcap (by omega) hr
  rw [hX] at key
  ihave #S614 := key $$ HG
  repeat mstep
  mcall S614 using [Hg Lo Hvt S0 S4 S8 Hsb]
  · iframe Hg Lo Hvt S0 S4 S8 Hsb
  icases HQ with ⟨%hrs, %p, %hl', %hhl, Hg, Lo, Hvt, S0, S4, S8, Hsb⟩
  subst hrs
  mcredits (50 * cfg.regularOpCost + R)
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
theorem f649_nu_fast (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
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
        (fun _ => 240 * cfg.regularOpCost +
          ScratchFast.pushCost cfg F capS (UInt32.ofNat acc.length))
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
  generalize hX : ScratchFast.pushCost cfg F capS (UInt32.ofNat acc.length) = X
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
  mcredits (120 * cfg.regularOpCost + (X + R))
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


/-- Instruction work outside appending: simple escapes have the tighter dispatch bound. -/
def workOps (l : List UInt8) : Nat :=
  if l.head? = some 0x75 then ParseEscapeSuccessCost.successOps l else 240

/-- The append charge used by an escape: push for simple escapes, UTF-8 slice append for Unicode. -/
def appendCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) : Nat :=
  if l.head? = some 0x75 then costExt cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (escK l))
  else ScratchFast.pushCost cfg F cap (UInt32.ofNat acc.length)

/-- A successful escape's tighter cost, preserving the general Unicode bounds. -/
def cost649 (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) : Nat :=
  workOps l * cfg.regularOpCost + appendCost cfg F cap acc l

/-- The non-append instruction work never exceeds the prior successful-escape bound. -/
theorem workOps_le (l : List UInt8) : workOps l ≤ ParseEscapeSuccessCost.successOps l := by
  unfold workOps
  split
  · omega
  · rename_i h
    have hnu : ∀ rest, l ≠ 0x75 :: rest := by
      intro rest hl
      subst l
      exact h rfl
    rw [ParseEscapeSuccessCost.successOps_nu l hnu]
    omega

/-- The 200-ops-per-consumed-byte bound remains valid with the tighter append charge. -/
theorem cost649_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l out : List UInt8) (m : Nat)
    (he : escDecode l = some (out, m)) :
    cost649 cfg F cap acc l ≤ 200 * (m + 1) * cfg.regularOpCost + appendCost cfg F cap acc l := by
  unfold cost649
  exact Nat.add_le_add_right (Nat.mul_le_mul_right cfg.regularOpCost
    ((workOps_le l).trans (ParseEscapeSuccessCost.successOps_le l out m he))) _

/-- Every successful escape has the original functional result at the tighter cost. -/
theorem f649_fast (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hvalid : (escDecode (bs.drop j)).isSome = true)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => cost649 cfg F capS acc (bs.drop j))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  by_cases hu : ∃ rest, bs.drop j = 0x75 :: rest
  · obtain ⟨rest, hrest⟩ := hu
    have hhead : (bs.drop j).head? = some 0x75 := by rw [hrest]; rfl
    simpa only [cost649, workOps, appendCost, hhead, ite_true, ParseEscapeSuccessCost.cost649] using
      ParseEscapeSuccessCost.f649_success (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg
        gt s de ptr sc ptrS capS idx bs acc j maxP hl live F hde hj hsc hlen hptr hs hcap hacc hvalid hr
  · have hhead : (bs.drop j).head? ≠ some 0x75 := by
      intro h
      cases hd : bs.drop j with
      | nil => simp [hd] at h
      | cons b rest =>
        simp only [hd, List.head?_cons, Option.some.injEq] at h
        exact hu ⟨rest, by rw [hd, h]⟩
    simpa only [cost649, workOps, appendCost, if_neg hhead] using
      f649_nu_fast (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg
        gt s de ptr sc ptrS capS idx bs acc j maxP hl live F hde hj hsc hlen hptr hs hcap hacc hvalid
        (fun rest h => hu ⟨rest, h⟩) hr

end Proof
end WNear.Binary.ParseEscapeFast
