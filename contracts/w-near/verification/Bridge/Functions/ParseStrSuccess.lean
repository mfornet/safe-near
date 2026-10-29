import Bridge.Functions.ParseStrEsc
import Bridge.Functions.StrSuccessCost

/-! # The successful string loop, with one final UTF-8 validation -/

namespace WNear.Binary.ParseStrSuccess

open WNear.Binary.ParseStr
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.FromUtf8 (res927 cost927)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4 f647_spec f648_spec_bad f657_eq)
open WNear.Binary.ScratchGrow (sbuf sgCode capAfter fAfter hlAfter roomRes costExt)
open WNear.Binary.ParseEscape (escDecode escK sbufE escCode res649)
open WNear.Binary.SerdeEsc (hexTable)


section L646e

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

set_option Elab.async false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000000 in
/-- Successful `parse_str`, with no error-cost reserves and one final UTF-8 check. -/
theorem f646_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de sc ptr idx ptrS capS : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hsp : 192 ≤ sp.toNat) (hi : i ≤ bs.length) (hcapS : capS.toNat < 2 ^ 25)
    (hroom : roomRun maxP hl capS [] (bs.drop i))
    (finalBytes finalRest : List UInt8) (hok : strRun (bs.drop i) [] = .ok finalBytes finalRest)
    (hvalidUtf : Utf8.utf8Ok finalBytes = true) :
    code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f646 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 192) 192 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] 0 ∗ sbuf n maxP hl live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] hexTable))
        (fun _ => costRun cfg F capS [] (bs.drop i) bs.length + 100 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 192) 192 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] hexTable ∗ resStr n maxP hl live F out de ptr sc ptrS capS ob bs i)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold code646 at Hk'
  icases Hk' with ⟨#HE, #HC, #F927, #F657, #F647, #F648, #F728⟩
  ihave #HE' := HE
  iunfold errCode at HE'
  icases HE' with ⟨#H310c, #H310, #H625, #H624, #H590, #H639, #F583, #H609, #H645, #H638⟩
  ihave #HC' := HC
  iunfold escCode at HC'
  icases HC' with ⟨#HG, -, -, -, #F649⟩
  ihave #HG' := HG
  iunfold sgCode at HG'
  icases HG' with ⟨-, -, -, -, -, -, -, -, -, #F613, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha583 := hm.funcs 583 (by decide)
  have ha613 := hm.funcs 613 (by decide)
  have ha647 := hm.funcs 647 (by decide)
  have ha648 := hm.funcs 648 (by decide)
  have ha649 := hm.funcs 649 (by decide)
  have ha728 := hm.funcs 728 (by decide)
  have ha927 := hm.funcs 927 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t36 : types[36]!.params.length = 6 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Ho, Hrd, S0, S4, S8, Hsb, He, Hw, Ht⟩
  subst hargs
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  simp only [f646]
  generalize hRl : 60 * cfg.regularOpCost + R = Rl
  rw [show costRun cfg F capS [] (bs.drop i) bs.length + 100 * cfg.regularOpCost + R =
    40 * cfg.regularOpCost + (costRun cfg F capS [] (bs.drop i) bs.length + Rl) by omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := costRun cfg F capS [] (bs.drop i) bs.length + Rl)
    (I := fun X fr => iprop(∃ (j : Nat) (acc : List UInt8) (p cap : UInt32) (hl' F' : Nat)
        (a4 a5 a6 a7 a8 a9 : UInt32),
      ⌜X = [] ∧ fr = fr646 inst mi out de sc (sp - 48) a4 a5 a6 a7 a8 a9 ∧ i ≤ j ∧ j ≤ bs.length ∧
        strRun (bs.drop j) acc = strRun (bs.drop i) [] ∧
        (acc = [] → j = i ∧ p = ptrS ∧ cap = capS ∧ hl' = hl ∧ F' = F) ∧ (j = i → acc = []) ∧ (j ≠ i → ¬ borrowed (bs.drop i)) ∧
        acc.length ≤ j - i ∧ cap.toNat ≤ max capS.toNat (2 * acc.length + 8) ∧ hl ≤ hl' ∧
        roomRun maxP hl' cap acc (bs.drop j)⌝ ∗
      credits Cg (costRun cfg F' cap acc (bs.drop j) bs.length + Rl) ∗ stk n (sp.toNat - 192) 192 ∗
      n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
      n ↦[wms][ 1062712 ] hexTable ∗ vt n 1057464 idx ta (A 578) ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩ ∗
      n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
      n ↦[i32][ de.toNat + 8 ] UInt32.ofNat j ∗ n ↦[wms][ ptr.toNat ] bs ∗
      n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗ n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗
      sbuf n maxP hl' live F' p cap acc)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%j, %acc, %p, %cap, %hl', %F', %a4, %a5, %a6, %a7, %a8, %a9,
      %⟨hX, hfr, hij, hjl, hrun, hacc0, hj0, hjb, haccl, hcapb, hhl, hroomj⟩,
      Hc, Hs, Ho, He, Hw, Ht, Hvt, Hg, D0, D4, D8, Hb, S0, S4, S8, Hsb⟩
    subst hX
    rw [hfr]
    simp only [fr646]
    clear hfr
    have hsplit := run_split (bs.drop j)
    have hcr := scan_le cfg F' cap acc (bs.drop j) bs.length
    generalize hbody : (bs.drop j).takeWhile plain = body at hsplit hcr
    generalize htail : (bs.drop j).dropWhile plain = tail at hsplit
    have hplain : ∀ b ∈ body, plain b = true := by rw [← hbody]; exact takeWhile_plain _
    have hstop : ∀ x rest, tail = x :: rest → plain x = false := fun x rest h =>
      dropWhile_head _ x rest (by rw [htail, h])
    have hil : j + body.length ≤ bs.length := by
      have := congrArg List.length hsplit; simp at this; omega
    have htl : j + body.length + tail.length = bs.length := by
      have := congrArg List.length hsplit; simp at this; omega
    have hsel : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat j)) = 0
        then Value.i32 (UInt32.ofNat j) else Value.i32 (UInt32.ofNat bs.length)) = Value.i32 (UInt32.ofNat bs.length) := by
      by_cases hib : j = bs.length
      · rw [hib]; split <;> rfl
      · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (UInt32.ofNat bs.length) (UInt32.ofNat j)) ≠ 0 := by
          simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
        rw [if_neg this]
    generalize hZ : costRun cfg F' cap acc (bs.drop j) bs.length - (500 + 30 * body.length) * cfg.regularOpCost = Z
    have hZ' : costRun cfg F' cap acc (bs.drop j) bs.length = (500 + 30 * body.length) * cfg.regularOpCost + Z := by
      have := Nat.le_add_right ((500 + 30 * body.length) * cfg.regularOpCost) 0
      omega
    rw [hZ', show (500 + 30 * body.length) * cfg.regularOpCost + Z + Rl =
      40 * cfg.regularOpCost + (30 * (j + body.length - j) * cfg.regularOpCost + 450 * cfg.regularOpCost +
        (Z + Rl) + 10 * cfg.regularOpCost) by
      rw [show j + body.length - j = body.length by omega]; simp only [Nat.add_mul]; omega]
    mstep; mstep [D4]; mstep; mstep; mstep [D8]
    mstep; mstep; mstep; mstep
    iapply mwpi_cons
    iapply FromUtf8.mwpi_select'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; omega
    inext
    iintro Hc
    rw [hsel]
    clear hsel
    mctrl_norm
    mstep; mstep; mstep [D0]; mstep; mstep; mstep
    mstep; mstep
    iapply MemCpy.mwpi_loop0 (Cg := Cg)
      (R := 30 * (j + body.length - j) * cfg.regularOpCost + 450 * cfg.regularOpCost + (Z + Rl))
      (I := invS n inst mi Cg cfg.regularOpCost 450 (Z + Rl) out de sc (sp - 48) (UInt32.ofNat bs.length)
        (UInt32.ofNat j) (UInt32.ofNat bs.length) ptr j body.length
        iprop(stk n (sp.toNat - 192) 192 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] hexTable ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
          n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 48)⟩ ∗
          n ↦[i32][ sc.toNat ] p ∗ n ↦[i32][ sc.toNat + 4 ] cap ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl' live F' p cap acc)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold invS at HI
      icases HI with ⟨%k, %l9, %⟨hX, hfr, hik, hkm⟩, Hc, D8, HP⟩
      subst hX
      rw [hfr]
      simp only [fr646]
      clear hfr
      icases HP with ⟨Hs, Ho, He, Hw, Ht, Hvt, D0, D4, Hb, Hg, S0, S4, S8, Hsb⟩
      by_cases hkl : k < bs.length
      · have hne : Numeric.bool (Numeric.irelop32 IRelOp.eq (UInt32.ofNat bs.length) (UInt32.ofNat k)) = 0 := by
          have hu : (UInt32.ofNat k).toNat = k := by simp; omega
          have hv : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
          generalize UInt32.ofNat k = u at hu ⊢
          generalize UInt32.ofNat bs.length = v at hv ⊢
          have : v ≠ u := fun e => by subst e; omega
          simp [Numeric.bool, Numeric.irelop32, this]
        have hbk : bs[k]? = (body ++ tail)[k - j]? := by
          rw [← hsplit, List.getElem?_drop]; congr 1; omega
        ihave Hb := MemCpy.memBytes_pick n ptr.toNat k bs hkl $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
        rw [hxk]
        rw [List.getElem?_eq_getElem hkl, hxk] at hbk
        have es : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
        have hx256 := x.toNat_lt
        by_cases hkm' : k < j + body.length
        · have hxb : plain x = true := by
            rw [List.getElem?_append_left (by omega)] at hbk
            exact hplain x (List.mem_of_getElem? hbk.symm)
          rw [show 30 * (j + body.length - k) * cfg.regularOpCost + 450 * cfg.regularOpCost + (Z + Rl) =
            480 * cfg.regularOpCost + (30 * (j + body.length - (k + 1)) * cfg.regularOpCost + (Z + Rl)) by
              rw [show j + body.length - k = (j + body.length - (k + 1)) + 1 by omega]
              simp only [Nat.mul_add, Nat.add_mul]; omega]
          generalize hZ2 : 30 * (j + body.length - (k + 1)) * cfg.regularOpCost = Z2
          mstep; mstep; mstep
          brn hne
          clear hne
          mstep; mstep; mstep
          mstep [Bk] with (simp [UInt32.toNat_add]; omega)
          simp only [SerdeKey.load8]
          ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          mstep; mstep; mstep
          ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
          icases He with ⟨E1, Ek, E2⟩
          mstep [Ek] with (simp [UInt32.toNat_add]; omega)
          rw [SerdeKey.load8, esc_at, if_pos hxb]
          ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
          · iframe E1 Ek E2
          rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
          brn rfl
          mstep; mstep; mstep; mstep; mstep
          mstep [D8]
          rw [SerdeRead.ofNat_succ k (by omega)]
          mstep
          simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iapply invS_intro n inst mi Cg cfg.regularOpCost 450 (Z + Rl) out de sc (sp - 48) _ _ _ ptr j body.length _ (k + 1) _
            (by omega) (by omega)
          iframe D8 Hs Ho He Hw Ht Hvt D0 D4 Hb Hg S0 S4 S8 Hsb
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · -- the scan stops at `x`, the first byte of `tail`
          have hk : k = j + body.length := by omega
          have htx : ∃ rest, tail = x :: rest := by
            rw [List.getElem?_append_right (by omega), show k - j - body.length = 0 by omega] at hbk
            cases htl' : tail with
            | nil => rw [htl'] at hbk; simp at hbk
            | cons y rest => rw [htl'] at hbk; simp at hbk; exact ⟨rest, by simp [hbk]⟩
          obtain ⟨rest, htx⟩ := htx
          have hxp := hstop x rest htx
          rw [show 30 * (j + body.length - k) * cfg.regularOpCost = 0 by rw [show j + body.length - k = 0 by omega]; simp,
            Nat.zero_add]
          mstep; mstep; mstep
          brn hne
          clear hne
          mstep; mstep; mstep
          mstep [Bk] with (simp [UInt32.toNat_add]; omega)
          simp only [SerdeKey.load8]
          ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          mstep; mstep; mstep
          ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
          icases He with ⟨E1, Ek, E2⟩
          mstep [Ek] with (simp [UInt32.toNat_add]; omega)
          rw [SerdeKey.load8, esc_at, if_neg (by rw [hxp]; decide)]
          ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
          · iframe E1 Ek E2
          rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
          iapply mwpi_cons
          iapply mwpi_br_if_taken'
          isplitr
          · ipureintro; exact ⟨rfl, by decide⟩
          mctrl_norm
          simp only [Post.mloop]
          mctrl_norm
          repeat mpay
          mstep; mstep; mstep; mstep
          by_cases hx92 : x.toNat = 92
          · -- `\`: an escape
            have hx : x = 0x5C := UInt8.toNat_inj.mp (by rw [hx92]; rfl)
            subst hx
            have h92 : Numeric.bool (Numeric.irelop32 IRelOp.eq (0x5C : UInt8).toUInt32 92) ≠ 0 := by decide
            have hd5c : (bs.drop j).dropWhile plain = 0x5C :: rest := by rw [htail, htx]
            have hnone : escDecode rest ≠ none := by
              intro he
              have ha := hrun.trans hok
              rw [strRun_cons _ _ 0x5C rest hd5c] at ha
              simp [he] at ha
            have hescvalid : (escDecode rest).isSome = true := by
              cases he : escDecode rest with
              | none => exact False.elim (hnone he)
              | some pr => rfl
            have hcb := costRun_esc cfg F' cap acc (bs.drop j) rest bs.length hd5c
            rw [costBase_esc cfg F' cap acc (bs.drop j) rest bs.length hd5c, hbody] at hcb
            have hrest : bs.drop (k + 1) = rest := by
              rw [hk, show j + body.length + 1 = j + (body.length + 1) by omega, ← List.drop_drop, hsplit, htx]; simp
            have hroom1 := (roomRun_unfold maxP hl' cap acc (bs.drop j)).mp hroomj
            rw [hbody] at hroom1
            iapply mwpi_cons
            iapply mwpi_br_if_taken'
            isplitr
            · ipureintro; exact ⟨rfl, h92⟩
            mctrl_norm
            repeat mpay
            icases stk_split n (sp.toNat - 192) 144 48 $$ Hs with ⟨T144, T48⟩
            rw [show sp.toNat - 192 + 144 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 24 24 $$ T48 with ⟨T24, T24b⟩
            icases stk_split n ((sp - 48).toNat + 24) 8 16 $$ T24b with ⟨T8e, T16b⟩
            iunfold stk at T8e
            icases T8e with ⟨%w8, %hw8, T8e⟩
            ihave T8e := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 24 = (sp - 48 + 24).toNat by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ T8e
            mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
            mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48 + 24) (UInt32.ofNat j)
              (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062216 w8 hw8 (by rw [UInt32.toNat_add, h48]; simp; omega)
              (by simp; omega) (by simp; omega)) using [T8e]
            · iframe T8e
            icases HQ with ⟨%hrs, P0, P4⟩
            subst hrs
            mcredits (300 * cfg.regularOpCost + (Z + Rl))
            ihave P0 := AllocNewCell.memBytes_addr (show (sp - 48 + 24).toNat = (sp - 48).toNat + 24 by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ P0
            ihave P4 := AllocNewCell.memBytes_addr (show (sp - 48 + 24).toNat + 4 = (sp - 48).toNat + 28 by
              rw [UInt32.toNat_add, h48]; simp; omega) $$ P4
            rw [show UInt32.ofNat k - UInt32.ofNat j = UInt32.ofNat body.length by
              apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
            mstep; mstep; mstep [P0]; mstep; mstep [P4]
            have hsplit' : bs.drop j = body ++ 0x5C :: rest := by rw [hsplit, htx]
            have hab : (acc ++ body).length = acc.length + body.length := List.length_append
            ihave Hb := U128From.memBytes_split n ptr.toNat j bs (by omega) $$ Hb
            icases Hb with ⟨B0, Bd⟩
            rw [hsplit']
            ihave Bd := U128From.memBytes_split n (ptr.toNat + j) body.length (body ++ 0x5C :: rest) (by simp) $$ Bd
            icases Bd with ⟨Bbody, Brest⟩
            rw [List.take_left' rfl, List.drop_left' rfl]
            ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + j = (ptr + UInt32.ofNat j).toNat by
              simp [UInt32.toNat_add]; omega) $$ Bbody
            icases stk_split n (sp.toNat - 192) 32 112 $$ T144 with ⟨T32a, T112⟩
            ihave T112 := stk_addr (show sp.toNat - 192 + 32 = (sp - 48).toNat - 112 by omega) $$ T112
            have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
            have hcapl : cap.toNat < 2 ^ 27 := by omega
            have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
              (sp - 48) sc (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) p cap idx maxP hl' live F' acc body
              (by omega) (by omega) hcapl (by rw [hm32]; omega) hm32.symm (by simp [UInt32.toNat_add]; omega) hroom1.2.1
            rw [show Z + Rl = costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) +
              (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl) by omega]
            mcall key using [Hg T112 Hvt S0 S4 S8 Hsb Bbody]
            · iframe Hg T112 Hvt S0 S4 S8 Hsb Bbody
            clear key
            icases HQ with ⟨%hrs, %p1, %hl1, %hhl1, Hg, T112, Hvt, S0, S4, S8, Hsb, Bbody⟩
            subst hrs
            rw [hm32]
            have hl1le := hlAfter_le _ _ _ _ _ hhl1
            have hroom2 := hroom1.2.2 hl1 hhl1
            have hroom3 := hroom2.2 rest hd5c
            mcredits (200 * cfg.regularOpCost + (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl))
            mstep; mstep [D8]
            mstep; mstep; mstep; mstep; mstep; mstep
            rw [SerdeRead.ofNat_succ k (by omega)]
            have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (k + 1)) (UInt32.ofNat k)) = 0 := by
              rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
            brn hov
            clear hov
            mstep; mstep; mstep [D8]
            ihave Hrd : rd n de ptr bs (k + 1) $$ [D0 D4 D8 B0 Bbody Brest]
            · iunfold rd, sliceRead
              iframe D0 D4 D8
              ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                simp [UInt32.toNat_add]; omega) $$ Bbody
              ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (92 :: rest) rfl $$ [Bbody Brest]
              · iframe Bbody Brest
              rw [← hsplit']
              ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
              · iframe B0 Bd
              rw [List.take_append_drop]
              iexact Bb
            ihave T144 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 192 + 32 by omega) $$ T112
            ihave T144 := stk_join n (sp.toNat - 192) 32 112 $$ [T32a T144]
            · iframe T32a T144
            ihave T144 := stk_addr (show sp.toNat - 192 = (sp - 48).toNat - 144 by omega) $$ T144
            rw [show UInt32.ofNat (acc.length + body.length) = UInt32.ofNat (acc ++ body).length by simp] at *
            generalize hcap1 : capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = cap1 at hroom3 hcb ⊢
            generalize hF1 : fAfter F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = F1 at hcb ⊢
            have hcap1b : cap1.toNat ≤ max capS.toNat (2 * (acc ++ body).length + 8) := by
              have := capAfter_le cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) (by omega) (by simp; omega)
              rw [hcap1] at this
              simp at this ⊢
              omega
            have key := ParseEscapeSuccessCost.f649_success (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt
              (sp - 48) de ptr sc p1 cap1 idx bs (acc ++ body) (k + 1) maxP hl1 live F1 hde (by omega) hsc (by omega)
              hptr (by omega) (by omega) (by simp; omega) (by rw [hrest]; exact hescvalid) (by rw [hrest]; exact hroom3.1)
            have hc649 : ParseEscapeSuccessCost.cost649 cfg F1 cap1 (acc ++ body) (bs.drop (k + 1)) = costEsc cfg F1 cap1 (acc ++ body) rest bs.length := by
              unfold costEsc; rw [hrest]
            rw [hc649] at key
            rw [show Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl =
              costEsc cfg F1 cap1 (acc ++ body) rest bs.length +
              (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                costEsc cfg F1 cap1 (acc ++ body) rest bs.length + Rl) by omega]
            mstep; mstep
            mcall key using [Hg T144 Hvt Hrd S0 S4 S8 Hsb Ht]
            · iframe Hg T144 Hvt Hrd S0 S4 S8 Hsb Ht
            clear key
            icases HQ with ⟨Hg, T144, Hvt, Ht, HQ⟩
            mcredits (150 * cfg.regularOpCost + (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                costEsc cfg F1 cap1 (acc ++ body) rest bs.length + Rl))
            cases he : escDecode rest with
            | none => simp [he] at hescvalid
            | some pr =>
              -- the escape decodes: back to the loop's head
              obtain ⟨eo, m⟩ := pr
              simp only [res649, hrest, he]
              icases HQ with ⟨%hrs, Hrd, %p2, %hl2, %hhl2, S0, S4, S8, Hsb⟩
              subst hrs
              obtain ⟨heo1, heom, hml⟩ := escDecode_len rest eo m he
              have hrl2 : rest.length = bs.length - (k + 1) := by rw [← hrest]; simp
              have hdr : bs.drop (k + 1 + m) = rest.drop m := by rw [← hrest, List.drop_drop]
              have hl2le := hlAfter_le _ _ _ _ _ hhl2
              have hkeo : escK rest = eo.length := by simp [ParseEscape.escK, he]
              rw [hkeo] at hroom3
              have hroom4 := hroom3.2 hl2 hhl2 eo m he
              have hrun' : strRun (bs.drop (k + 1 + m)) (acc ++ body ++ eo) = strRun (bs.drop i) [] := by
                rw [hdr, ← hrun, strRun_cons (bs.drop j) acc 0x5C rest (by rw [htail, htx]), hbody]
                simp [he]
              have hnb : ¬ borrowed (bs.drop i) := by
                by_cases hji : j = i
                · subst hji; unfold borrowed; rw [htail, htx]; simp
                · exact hjb hji
              mstep; mstep
              iapply mwpi_cons
              iapply mwpi_br_if_taken'
              isplitr
              · ipureintro; exact ⟨rfl, by decide⟩
              mctrl_norm
              (try simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil])
              iapply pure_pay_intro'
              isplitl [Hc]
              · iexact Hc
              isplitr
              · ipureintro; exact ⟨by simp, by omega⟩
              inext
              iintro Hc
              iunfold rd, sliceRead at Hrd
              icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
              try rw [← List.append_assoc acc body eo]
              iexists k + 1 + m, acc ++ body ++ eo, p2, capAfter cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat eo.length),
                hl2, fAfter F1 cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat eo.length), _, _, _, _, _, _
              isplitr
              · ipureintro
                have hcap2 := capAfter_le cap1 (UInt32.ofNat (acc ++ body).length) (UInt32.ofNat eo.length) (by omega)
                  (by simp; omega)
                refine ⟨by first | rfl | trivial, by first | rfl | trivial, by omega, by omega, hrun',
                  fun h => absurd (congrArg List.length h) (by simp only [List.length_append, List.length_nil]; omega),
                  fun h => absurd h (by omega),
                  fun _ => hnb, by simp; omega, ?_, by omega, by rw [hdr]; exact hroom4⟩
                simp at hcap2 ⊢; omega
              iframe Ho He Hw Ht Hvt Hg D0 D4 D8 Hb S0 S4 Hsb
              isplitl [Hc]
              · iapply BorrowMut.credits_le
                iframe Hc
                ipureintro
                simp only [he] at hcb
                rw [hdr]
                omega
              isplitr [S8]
              · ihave P0 := stk_word n ((sp - 48).toNat + 24) _ $$ P0
                ihave P4 := stk_word n ((sp - 48).toNat + 28) _ $$ P4
                ihave P8 := stk_join n ((sp - 48).toNat + 24) 4 4 $$ [P0 P4]
                · iframe P0 P4
                ihave T24b := stk_join n ((sp - 48).toNat + 24) 8 16 $$ [P8 T16b]
                · iframe P8 T16b
                ihave S48 := stk_join n (sp - 48).toNat 24 24 $$ [T24 T24b]
                · iframe T24 T24b
                ihave T144 := stk_addr (show (sp - 48).toNat - 144 = sp.toNat - 192 by omega) $$ T144
                ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                iapply stk_join n (sp.toNat - 192) 144 48
                iframe T144 S48
              rw [show UInt32.ofNat ((acc ++ body).length + eo.length) = UInt32.ofNat (acc ++ body ++ eo).length by simp only [List.length_append]]
              iexact S8
          have h92 : Numeric.bool (Numeric.irelop32 IRelOp.eq x.toUInt32 92) = 0 := by rw [eq92, if_neg hx92]
          brn h92
          by_cases hx34 : x.toNat = 34
          · -- `"`: the end of the string
            have hx : x = 0x22 := UInt8.toNat_inj.mp (by rw [hx34]; rfl)
            subst hx
            have hres : strRun (bs.drop i) [] = .ok (acc ++ body) rest := by
              rw [← hrun, strRun_cons _ _ 0x22 rest (by rw [htail, htx]), hbody]; simp
            have hcb := costRun_stop cfg F' cap acc (bs.drop j) bs.length (by
              intro r; rw [htail, htx]; simp)
            rw [costBase_close cfg F' cap acc (bs.drop j) rest bs.length (by rw [htail, htx]),
              hbody, Nat.add_mul (500 + 30 * body.length)] at hcb
            have hrl : bs.length - rest.length = k + 1 := by rw [htx] at htl; simp at htl; omega
            icases stk_split n (sp.toNat - 192) 144 48 $$ Hs with ⟨T144, T48⟩
            rw [show sp.toNat - 192 + 144 = (sp - 48).toNat by omega]
            icases stk_split n (sp - 48).toNat 8 40 $$ T48 with ⟨T8, T40⟩
            icases stk_split n ((sp - 48).toNat + 8) 24 16 $$ T40 with ⟨T24, T16⟩
            icases stk_split n ((sp - 48).toNat + 8 + 24) 12 4 $$ T16 with ⟨T12, T4⟩
            iunfold stk at T8 T12
            icases T8 with ⟨%s8, %hs8, T8⟩
            icases T12 with ⟨%s12, %hs12, T12⟩
            mstep; mstep; mstep
            brn (by decide)
            mstep; mstep
            mstep [S8]
            by_cases hae : acc = []
            · -- no escape: the slice is borrowed
              obtain ⟨hji, hp, hcap', hhl', hF'⟩ := hacc0 hae
              subst hp hcap' hhl' hF' hae hji
              have hbor : borrowed (bs.drop j) := by unfold borrowed; rw [htail, htx]; rfl
              simp only [List.length_nil, List.nil_append, Nat.zero_add] at hres hcb hcr ⊢
              brn rfl
              mstep; mstep; mstep; mstep; mstep; mstep
              mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48) (UInt32.ofNat j)
                (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062248 s8 hs8 (by omega)
                (by simp; omega) (by simp; omega)) using [T8]
              · iframe T8
              icases HQ with ⟨%hrs, P0, P4⟩
              subst hrs
              mcredits (300 * cfg.regularOpCost + (Z + Rl))
              mstep; mstep; mstep
              mstep [D8]
              mstep; mstep; mstep; mstep; mstep; mstep
              rw [SerdeRead.ofNat_succ k (by omega)]
              have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (k + 1)) (UInt32.ofNat k)) = 0 := by
                rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
              brn hov
              clear hov
              mstep; mstep [P4]; mstep; mstep; mstep [P0]; mstep
              mstep; mstep
              mstep [D8]
              rw [show UInt32.ofNat k - UInt32.ofNat j = UInt32.ofNat body.length by
                apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
              mstep; mstep; mstep; mstep; mstep; mstep
              have h32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
              have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
              have hsplit' : bs.drop j = body ++ 0x22 :: rest := by rw [hsplit, htx]
              by_cases hutf : Utf8.utf8Ok body = true
              · -- `Ok(Borrowed)`
                ihave Hb := U128From.memBytes_split n ptr.toNat j bs (by omega) $$ Hb
                icases Hb with ⟨B0, Bd⟩
                rw [hsplit']
                ihave Bd := U128From.memBytes_split n (ptr.toNat + j) body.length (body ++ 0x22 :: rest) (by simp) $$ Bd
                icases Bd with ⟨Bbody, Brest⟩
                rw [List.take_left' rfl, List.drop_left' rfl]
                ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + j = (ptr + UInt32.ofNat j).toNat by
                  simp [UInt32.toNat_add]; omega) $$ Bbody
                ihave T12 := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                  rw [UInt32.toNat_add, h48]; simp; omega) $$ T12
                icases stk_split n (sp.toNat - 192) 112 32 $$ T144 with ⟨T112, T32⟩
                ihave T32 := stk_addr (show sp.toNat - 192 + 112 = (sp - 48).toNat - 32 by omega) $$ T32
                have hK3 : (12 + cost648 (UInt32.ofNat body.length).toNat) * cfg.regularOpCost =
                    52 * cfg.regularOpCost + cost927 body.length * cfg.regularOpCost := by
                  rw [hm32]; unfold cost648; simp only [Nat.add_mul]; omega
                rw [show Z + Rl = cost927 body.length * cfg.regularOpCost +
                  (Z - cost927 body.length * cfg.regularOpCost + Rl) by omega]
                mcall (f648_spec_valid cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg (A 927) ha927 (by omega) Cg gt
                  (sp - 48) (sp - 48 + 32) de (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) s12 body hs12
                  (by rw [UInt32.toNat_add, h48]; simp; omega) (by simp; omega) (by simp [UInt32.toNat_add]; omega)
                  (by omega) hutf) using [Hg T32 T12 Bbody Hw]
                · iframe Hg T32 T12 Bbody Hw
                rw [hK3]
                mcredits (60 * cfg.regularOpCost + (Z - cost927 body.length * cfg.regularOpCost + Rl))
                icases HQ with ⟨%hrs, Hg, T32, Q0, Q4, Q8, Bbody, Hw⟩
                subst hrs
                rw [h32]
                icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
                icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, Ho⟩
                icases U128From.memBytes_split n (out.toNat + 4 + 4) 4 ((ob.drop 4).drop 4) (by simp; omega) $$ Ho with ⟨O8, O12⟩
                mstep; mstep [Q4]; mstep
                mstep; mstep; mstep [Q0]; mstep; mstep
                brn (by decide)
                mstep; mstep; mstep; mstep
                mstep [O8] with (simp [UInt32.toNat_add]; omega)
                mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
                mstep [Q8] with (simp [UInt32.toNat_add]; omega)
                mstep [O12] with (simp [UInt32.toNat_add]; omega)
                mstep; mstep; mstep; mstep
                mstep; mstep
                mstep [O0]
                mstep; mstep
                mstep [O4]
                mstep
                (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
                mstep; mstep; mstep; mstep [Hg]
                rw [show sp - 48 + 48 = sp by simp]
                repeat mstep
                isplitl [Hc]
                · iapply BorrowMut.credits_le
                  iframe Hc
                  ipureintro; omega
                isplitr
                · ipureintro; trivial
                iframe Hg Hvt He Hw Ht
                isplitr [O0 O4 O8 O12 D0 D4 D8 B0 Bbody Brest S0 S4 S8 Hsb]
                · ihave P0 := stk_word n (sp - 48).toNat _ $$ P0
                  ihave P4 := stk_word n ((sp - 48).toNat + 4) _ $$ P4
                  ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
                  ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
                  ihave Q8 := stk_word n ((sp - 48).toNat + 32 + 8) _ $$ Q8
                  ihave P8 := stk_join n (sp - 48).toNat 4 4 $$ [P0 P4]
                  · iframe P0 P4
                  ihave Q48 := stk_join n ((sp - 48).toNat + 32 + 4) 4 4 $$ [Q4 Q8]
                  · rw [show (sp - 48).toNat + 32 + 4 + 4 = (sp - 48).toNat + 32 + 8 by omega]; iframe Q4 Q8
                  ihave Q12 := stk_join n ((sp - 48).toNat + 32) 4 8 $$ [Q0 Q48]
                  · iframe Q0 Q48
                  ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [P8 T24]
                  · iframe P8 T24
                  ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                  · iframe S32' Q12
                  ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 T4]
                  · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 T4
                  ihave S80' := stk_join n ((sp - 48).toNat - 32) 32 48 $$ [T32 S48]
                  · rw [show (sp - 48).toNat - 32 + 32 = (sp - 48).toNat by omega]; iframe T32 S48
                  ihave S80' := stk_addr (show (sp - 48).toNat - 32 = sp.toNat - 192 + 112 by omega) $$ S80'
                  iapply stk_join n (sp.toNat - 192) 112 80
                  iframe T112 S80'
                iunfold resStr
                rw [hres]
                simp only [if_pos hutf, if_pos hbor]
                rw [hrl]
                rw [show out.toNat + 4 + 4 + 4 = out.toNat + 12 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
                iframe O0 O4 O8 O12 S0 S4 S8 Hsb
                iunfold rd, sliceRead
                rw [show (k + 1) = k + 1 from rfl]
                iframe D0 D4 D8
                ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                  simp [UInt32.toNat_add]; omega) $$ Bbody
                ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (34 :: rest) rfl $$ [Bbody Brest]
                · iframe Bbody Brest
                rw [← hsplit']
                ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
                · iframe B0 Bd
                rw [List.take_append_drop]
                iexact Bb
              · have heq := StrOut.ok.inj (hres.symm.trans hok)
                have hgood : Utf8.utf8Ok body = true := by rw [heq.1]; exact hvalidUtf
                exact False.elim (hutf hgood)
            · -- the scratch holds the escapes' bytes: append the rest, `Ok(Copied)`
              have hji : j ≠ i := fun e => hae (hj0 e)
              have hnb := hjb hji
              have hal : 0 < acc.length := List.length_pos_iff.mpr hae
              have hlenu : (UInt32.ofNat acc.length) ≠ 0 := fun e => by
                have := congrArg UInt32.toNat e; simp at this; omega
              iapply mwpi_cons
              iapply mwpi_br_if_taken'
              isplitr
              · ipureintro; exact ⟨rfl, hlenu⟩
              mctrl_norm
              repeat mpay
              icases stk_split n ((sp - 48).toNat + 8) 8 16 $$ T24 with ⟨T8b, T16⟩
              icases stk_split n ((sp - 48).toNat + 8 + 8) 8 8 $$ T16 with ⟨T8c, T8d⟩
              iunfold stk at T8b T8c
              icases T8b with ⟨%u8, %hu8, T8b⟩
              icases T8c with ⟨%v8, %hv8, T8c⟩
              ihave T8c := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 8 = (sp - 48 + 16).toNat by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ T8c
              mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
              mcall (f583_spec cfg (lim := lim) (d + 1) types[36]! (by rfl) inst mi n hn Cg (sp - 48 + 16) (UInt32.ofNat j)
                (UInt32.ofNat k) ptr (UInt32.ofNat bs.length) 1062280 v8 hv8 (by rw [UInt32.toNat_add, h48]; simp; omega)
                (by simp; omega) (by simp; omega)) using [T8c]
              · iframe T8c
              icases HQ with ⟨%hrs, P0, P4⟩
              subst hrs
              mcredits (300 * cfg.regularOpCost + (Z + Rl))
              ihave P0 := AllocNewCell.memBytes_addr (show (sp - 48 + 16).toNat = (sp - 48).toNat + 16 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ P0
              ihave P4 := AllocNewCell.memBytes_addr (show (sp - 48 + 16).toNat + 4 = (sp - 48).toNat + 20 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ P4
              rw [show UInt32.ofNat k - UInt32.ofNat j = UInt32.ofNat body.length by
                apply UInt32.toNat_inj.mp; rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega]
              mstep; mstep; mstep [P0]; mstep; mstep [P4]
              -- the body's bytes, for 613
              have hsplit' : bs.drop j = body ++ 0x22 :: rest := by rw [hsplit, htx]
              have hab : (acc ++ body).length = acc.length + body.length := List.length_append
              ihave Hb := U128From.memBytes_split n ptr.toNat j bs (by omega) $$ Hb
              icases Hb with ⟨B0, Bd⟩
              rw [hsplit']
              ihave Bd := U128From.memBytes_split n (ptr.toNat + j) body.length (body ++ 0x22 :: rest) (by simp) $$ Bd
              icases Bd with ⟨Bbody, Brest⟩
              rw [List.take_left' rfl, List.drop_left' rfl]
              ihave Bbody := AllocNewCell.memBytes_addr (show ptr.toNat + j = (ptr + UInt32.ofNat j).toNat by
                simp [UInt32.toNat_add]; omega) $$ Bbody
              icases stk_split n (sp.toNat - 192) 32 112 $$ T144 with ⟨T32a, T112⟩
              ihave T112 := stk_addr (show sp.toNat - 192 + 32 = (sp - 48).toNat - 112 by omega) $$ T112
              have hroom1 := (roomRun_unfold maxP hl' cap acc (bs.drop j)).mp hroomj
              rw [hbody] at hroom1
              have hm32 : (UInt32.ofNat body.length).toNat = body.length := by simp; omega
              have hcapl : cap.toNat < 2 ^ 27 := by omega
              have key := ScratchGrow.f613_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
                (sp - 48) sc (ptr + UInt32.ofNat j) (UInt32.ofNat body.length) p cap idx maxP hl' live F' acc body
                (by omega) (by omega) hcapl (by rw [hm32]; omega) hm32.symm (by simp [UInt32.toNat_add]; omega) hroom1.2.1
              rw [show Z + Rl = costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) +
                (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl) by omega]
              mcall key using [Hg T112 Hvt S0 S4 S8 Hsb Bbody]
              · iframe Hg T112 Hvt S0 S4 S8 Hsb Bbody
              clear key
              icases HQ with ⟨%hrs, %p1, %hl1, %hhl1, Hg, T112, Hvt, S0, S4, S8, Hsb, Bbody⟩
              subst hrs
              rw [hm32]
              generalize hcap1 : capAfter cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = cap1
              generalize hF1 : fAfter F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) = F1
              have hl1le := hlAfter_le _ _ _ _ _ hhl1
              mcredits (200 * cfg.regularOpCost + (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl))
              mstep; mstep
              mstep; mstep [D8]
              mstep; mstep; mstep; mstep; mstep; mstep
              rw [SerdeRead.ofNat_succ k (by omega)]
              have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (k + 1)) (UInt32.ofNat k)) = 0 := by
                rw [FromUtf8.ltu_ofNat _ _ (by omega)]; simp; omega
              brn hov
              clear hov
              mstep; mstep; mstep [D8]
              ihave T8b := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 = (sp - 48 + 8).toNat by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ T8b
              mstep; mstep; mstep; mstep
              mcall (f728_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (sp - 48 + 8) sc p1
                (UInt32.ofNat (acc.length + body.length)) u8 hu8) using [T8b S0 S8]
              · iframe T8b S0 S8
              icases HQ with ⟨%hrs, R0, R4, S0, S8⟩
              subst hrs
              ihave R0 := AllocNewCell.memBytes_addr (show (sp - 48 + 8).toNat = (sp - 48).toNat + 8 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ R0
              ihave R4 := AllocNewCell.memBytes_addr (show (sp - 48 + 8).toNat + 4 = (sp - 48).toNat + 12 by
                rw [UInt32.toNat_add, h48]; simp; omega) $$ R4
              mstep; mstep; mstep; mstep; mstep; mstep [R0]; mstep; mstep [R4]
              have h32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
              have hm2 : (UInt32.ofNat (acc.length + body.length)).toNat = (acc ++ body).length := by simp; omega
              have hres' : strRun (bs.drop i) [] = .ok (acc ++ body) rest := hres
              by_cases hutf : Utf8.utf8Ok (acc ++ body) = true
              · -- `Ok(Copied)`
                ihave T12 := AllocNewCell.memBytes_addr (show (sp - 48).toNat + 8 + 24 = (sp - 48 + 32).toNat by
                  rw [UInt32.toNat_add, h48]; simp; omega) $$ T12
                icases sbuf_bytes $$ Hsb with ⟨%hpb, Bs, Hsw⟩
                icases stk_split n ((sp - 48).toNat - 112) 80 32 $$ T112 with ⟨T80, T32⟩
                ihave T32 := stk_addr (show (sp - 48).toNat - 112 + 80 = (sp - 48).toNat - 32 by omega) $$ T32
                have hK3 : (12 + cost648 (UInt32.ofNat (acc.length + body.length)).toNat) * cfg.regularOpCost =
                    52 * cfg.regularOpCost + cost927 (acc.length + body.length) * cfg.regularOpCost := by
                  rw [hm2]; unfold cost648; simp only [Nat.add_mul, List.length_append]; omega
                rw [show Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) + Rl =
                  cost927 (acc.length + body.length) * cfg.regularOpCost +
                  (Z - costExt cfg F' cap (UInt32.ofNat acc.length) (UInt32.ofNat body.length) -
                    cost927 (acc.length + body.length) * cfg.regularOpCost + Rl) by omega]
                mcall (f648_spec_valid cfg (lim := lim) (d + 1) types[45]! (by rfl) inst mi n g hn hg (A 927) ha927 (by omega) Cg gt
                  (sp - 48) (sp - 48 + 32) de p1 (UInt32.ofNat (acc.length + body.length)) s12 (acc ++ body) hs12
                  (by rw [h32]; omega) hm2.symm (by rw [hm2]; omega) (by omega) hutf) using [Hg T32 T12 Bs Hw]
                · iframe Hg T32 T12 Bs Hw
                rw [hK3]
                mcredits (60 * cfg.regularOpCost + Rl)
                icases HQ with ⟨%hrs, Hg, T32, Q0, Q4, Q8, Bs, Hw⟩
                subst hrs
                rw [h32]
                icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
                icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, Ho⟩
                icases U128From.memBytes_split n (out.toNat + 4 + 4) 4 ((ob.drop 4).drop 4) (by simp; omega) $$ Ho with ⟨O8, O12⟩
                mstep; mstep [Q4]; mstep
                mstep; mstep; mstep [Q0]; mstep; mstep
                brn (by decide)
                mstep; mstep; mstep; mstep
                mstep [O8] with (simp [UInt32.toNat_add]; omega)
                mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
                mstep [Q8] with (simp [UInt32.toNat_add]; omega)
                mstep [O12] with (simp [UInt32.toNat_add]; omega)
                mstep; mstep; mstep; mstep
                mstep; mstep
                mstep [O0]
                mstep; mstep
                mstep [O4]
                mstep
                (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
                mstep; mstep; mstep; mstep [Hg]
                rw [show sp - 48 + 48 = sp by simp]
                repeat mstep
                isplitl [Hc]
                · iapply BorrowMut.credits_le
                  iframe Hc
                  ipureintro; omega
                isplitr
                · ipureintro; trivial
                iframe Hg Hvt He Hw Ht
                isplitr [O0 O4 O8 O12 D0 D4 D8 B0 Bbody Brest S0 S4 S8 Hsw Bs]
                · ihave P0 := stk_word n ((sp - 48).toNat + 16) _ $$ P0
                  ihave P4 := stk_word n ((sp - 48).toNat + 20) _ $$ P4
                  ihave R0 := stk_word n ((sp - 48).toNat + 8) _ $$ R0
                  ihave R4 := stk_word n ((sp - 48).toNat + 12) _ $$ R4
                  ihave Q0 := stk_word n ((sp - 48).toNat + 32) _ $$ Q0
                  ihave Q4 := stk_word n ((sp - 48).toNat + 32 + 4) _ $$ Q4
                  ihave Q8 := stk_word n ((sp - 48).toNat + 32 + 8) _ $$ Q8
                  ihave R8 := stk_join n ((sp - 48).toNat + 8) 4 4 $$ [R0 R4]
                  · iframe R0 R4
                  ihave P8 := stk_join n ((sp - 48).toNat + 16) 4 4 $$ [P0 P4]
                  · iframe P0 P4
                  ihave T16 := stk_join n ((sp - 48).toNat + 8 + 8) 8 8 $$ [P8 T8d]
                  · rw [show (sp - 48).toNat + 8 + 8 = (sp - 48).toNat + 16 by omega]; iframe P8 T8d
                  ihave T24 := stk_join n ((sp - 48).toNat + 8) 8 16 $$ [R8 T16]
                  · iframe R8 T16
                  ihave Q48 := stk_join n ((sp - 48).toNat + 32 + 4) 4 4 $$ [Q4 Q8]
                  · rw [show (sp - 48).toNat + 32 + 4 + 4 = (sp - 48).toNat + 32 + 8 by omega]; iframe Q4 Q8
                  ihave Q12 := stk_join n ((sp - 48).toNat + 32) 4 8 $$ [Q0 Q48]
                  · iframe Q0 Q48
                  ihave T8 := stk_intro n _ _ $$ T8
                  rw [hs8]
                  ihave S32' := stk_join n (sp - 48).toNat 8 24 $$ [T8 T24]
                  · iframe T8 T24
                  ihave S44 := stk_join n (sp - 48).toNat 32 12 $$ [S32' Q12]
                  · iframe S32' Q12
                  ihave S48 := stk_join n (sp - 48).toNat 44 4 $$ [S44 T4]
                  · rw [show (sp - 48).toNat + 44 = (sp - 48).toNat + 8 + 24 + 12 by omega]; iframe S44 T4
                  ihave T32 := stk_addr (show (sp - 48).toNat - 32 = (sp - 48).toNat - 112 + 80 by omega) $$ T32
                  ihave T112 := stk_join n ((sp - 48).toNat - 112) 80 32 $$ [T80 T32]
                  · iframe T80 T32
                  ihave T112 := stk_addr (show (sp - 48).toNat - 112 = sp.toNat - 192 + 32 by omega) $$ T112
                  ihave T144 := stk_join n (sp.toNat - 192) 32 112 $$ [T32a T112]
                  · iframe T32a T112
                  ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 192 + 144 by omega) $$ S48
                  iapply stk_join n (sp.toNat - 192) 144 48
                  iframe T144 S48
                iunfold resStr
                rw [hres']
                simp only [if_pos hutf, if_neg hnb]
                rw [hrl]
                rw [show out.toNat + 4 + 4 + 4 = out.toNat + 12 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
                rw [show UInt32.ofNat (acc.length + body.length) = UInt32.ofNat (acc ++ body).length by simp]
                iframe O0 O12
                isplitr [O4 O8 S0 S4 S8 Hsw Bs]
                · iunfold rd, sliceRead
                  iframe D0 D4 D8
                  ihave Bbody := AllocNewCell.memBytes_addr (show (ptr + UInt32.ofNat j).toNat = ptr.toNat + j by
                    simp [UInt32.toNat_add]; omega) $$ Bbody
                  ihave Bd := U128From.memBytes_join n (ptr.toNat + j) body.length body (34 :: rest) rfl $$ [Bbody Brest]
                  · iframe Bbody Brest
                  rw [← hsplit']
                  ihave Bb := U128From.memBytes_join n ptr.toNat j (bs.take j) (bs.drop j) (by simp; omega) $$ [B0 Bd]
                  · iframe B0 Bd
                  rw [List.take_append_drop]
                  iexact Bb
                iexists p1, cap1, hl1, F1
                isplitr
                · ipureintro; omega
                iframe O4 O8 S0 S4 S8
                iapply Hsw $$ Bs
              · have heq := StrOut.ok.inj (hres'.symm.trans hok)
                have hgood : Utf8.utf8Ok (acc ++ body) = true := by rw [heq.1]; exact hvalidUtf
                exact False.elim (hutf hgood)
          · -- a control byte: `ControlCharacterWhileParsingString`
            have hx22 : x ≠ 0x22 := fun e => hx34 (by rw [e]; rfl)
            have hx5c : x ≠ 0x5C := fun e => hx92 (by rw [e]; rfl)
            have hres : strRun (bs.drop i) [] = .ctrl := by
              rw [← hrun, strRun_cons _ _ x rest (by rw [htail, htx])]; simp [hx22, hx5c]
            rw [hok] at hres
            cases hres
      · -- EOF: the scan reaches the end of the input
        have hk : k = bs.length := by omega
        have htn : tail = [] := by rw [← List.length_eq_zero_iff]; omega
        have hres : strRun (bs.drop i) [] = .eof := by rw [← hrun, strRun_nil _ _ (by rw [htail, htn])]
        rw [hok] at hres
        cases hres
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      have e1 : (30 * body.length + 450) * cfg.regularOpCost = 30 * body.length * cfg.regularOpCost + 450 * cfg.regularOpCost :=
        Nat.add_mul _ _ _
      have e2 : 30 * (j + body.length - j) * cfg.regularOpCost = 30 * body.length * cfg.regularOpCost := by
        rw [show j + body.length - j = body.length by omega]
      ipureintro; omega
    inext
    iintro Hc
    iapply invS_intro n inst mi Cg cfg.regularOpCost 450 (Z + Rl) out de sc (sp - 48) _ _ _ ptr j body.length _ j _
      le_rfl (by omega)
    iframe Hc D8 Hs Ho He Hw Ht Hvt D0 D4 Hb Hg S0 S4 S8 Hsb
  · isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    inext
    iintro Hc
    iexists i, [], ptrS, capS, hl, F, 0, 0, 0, 0, 0, 0
    iframe Hc Hs Ho He Hw Ht Hvt Hg D0 D4 D8 Hb S0 S4 Hsb
    isplitr
    · ipureintro
      refine ⟨rfl, rfl, le_rfl, hi, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun h => absurd rfl h, by simp, by simp, le_rfl, hroom⟩
    iexact S8

end L646e

end WNear.Binary.ParseStrSuccess
