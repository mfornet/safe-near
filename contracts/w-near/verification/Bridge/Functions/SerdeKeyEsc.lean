import Bridge.Functions.SerdeValueState
import Bridge.Functions.SerdeNextKey

/-!
# Object keys through the general successful string reader

The key visitor borrows decoded bytes until the field comparison finishes. Its
continuation retains the changed scratch allocation, with logical contents
forgotten so the next key or value may clear and reuse it.
-/

namespace WNear.Binary.SerdeKeyEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (strRun borrowed plain roomRun code646)
open WNear.Binary.ParseStrSuccess (appendChunks growthBudget resStrTraced)
open WNear.Binary.ScratchGrow (sbuf endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (tables scratchPre)

/-- A successful borrowed string is exactly the initial plain slice and its closing quote. -/
theorem borrowed_split (l bytes rest : List UInt8) (hb : borrowed l)
    (hok : strRun l [] = .ok bytes rest) : l = bytes ++ (0x22 :: rest) := by
  unfold borrowed at hb
  cases hd : l.dropWhile plain with
  | nil => simp [hd] at hb
  | cons b tail =>
    simp only [hd, List.head?_cons, Option.some.injEq] at hb
    subst b
    rw [ParseStr.strRun_cons _ _ _ _ hd] at hok
    simp only [ite_true, List.nil_append, ParseStr.StrOut.ok.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    exact (List.takeWhile_append_dropWhile (p := plain) (l := l)).symm.trans (by rw [hd])

/-- Successful key parsing, including the concrete scratch growth budget. -/
def keyCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (q : Nat) : Nat :=
  (500 + 470 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost +
    growthBudget cfg F (ScratchGrow.growthCount cap 0 (appendChunks (bs.drop q) [])) bytes.length

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Forget the logical contents, retaining the allocation and all its bytes as spare capacity. -/
theorem sbuf_clear (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (p cap : UInt32) (bytes : List UInt8) :
    sbuf (GF := GF) n maxP hl live F p cap bytes ⊢ sbuf n maxP hl live F p cap [] := by
  iintro H
  iunfold sbuf at H
  icases H with ⟨%hb, Hb, ⟨%junk, %hj, Hj⟩, Hheap⟩
  ihave Hall := U128From.memBytes_join n p.toNat bytes.length bytes junk rfl $$ [Hb Hj]
  · iframe Hb Hj
  iunfold sbuf
  isplitr
  · ipureintro; exact ⟨by simp, hb.2⟩
  isplitl []
  · iapply ScratchGrow.memBytes_nil
  simp only [List.length_nil, Nat.add_zero, Nat.sub_zero]
  isplitl [Hall]
  · iexists bytes ++ junk
    iframe Hall
    ipureintro; simp only [List.length_append]; omega
  iexact Hheap

/-- Reader and reusable scratch after the field matcher has returned the key bytes. -/
def keyState (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr ptrS capS : UInt32) (bs bytes rest : List UInt8) (q : Nat) : IProp GF :=
  iprop(rd n de ptr bs (bs.length - rest.length) ∗
    if borrowed (bs.drop q) then scratchPre n maxP hl live F de ptrS capS 0
    else ∃ (p cap : UInt32) (hl' F' : Nat),
      ⌜hl ≤ hl' ∧ cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧
        F' = endFreeBound F capS 0 (appendChunks (bs.drop q) []) ∧
        hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop q) []) * 65536⌝ ∗
      scratchPre n maxP hl' live F' de p cap (UInt32.ofNat bytes.length))

/-- Lend either input-backed or scratch-backed key bytes until the field visitor returns them. -/
theorem result_lend (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (out de ptr ptrS capS : UInt32) (ob bs bytes rest : List UInt8) (q : Nat)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hq : q ≤ bs.length)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hok : strRun (bs.drop q) [] = .ok bytes rest) (hu : Utf8.utf8Ok bytes = true) :
    resStrTraced (GF := GF) n maxP hl live F out de ptr (de + 12) ptrS capS ob bs q ⊢
      ∃ (t p : UInt32), ⌜p.toNat + bytes.length ≤ 2 ^ 32 ∧ bytes.length < 2 ^ 32⌝ ∗
        n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] t ∗
        n ↦[i32][ out.toNat + 8 ] p ∗ n ↦[i32][ out.toNat + 12 ] UInt32.ofNat bytes.length ∗
        n ↦[wms][ p.toNat ] bytes ∗
        (n ↦[wms][ p.toNat ] bytes -∗ keyState n maxP hl live F de ptr ptrS capS bs bytes rest q) := by
  have hsc : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hsize := SerdeDeStrEsc.strRun_size (bs.drop q) [] bytes rest hok
  simp only [List.length_nil, Nat.zero_add, List.length_drop] at hsize
  iintro H
  iunfold resStrTraced at H
  simp only [hok, if_pos hu, hsc]
  by_cases hb : borrowed (bs.drop q)
  · simp only [if_pos hb]
    icases H with ⟨O0, Hrd, O12, O4, O8, S0, S4, S8, Hsb⟩
    have hpq : (ptr + UInt32.ofNat q).toNat = ptr.toNat + q := by
      simp [UInt32.toNat_add]; omega
    icases SerdeNextKey.rd_lend n de ptr bs bytes (0x22 :: rest)
      (bs.length - rest.length) q (borrowed_split _ _ _ hb hok) hq $$ Hrd with ⟨Hb, Hwand⟩
    iexists 0, ptr + UInt32.ofNat q
    rw [hpq]
    isplitr
    · ipureintro; omega
    iframe O0 O4 O8 O12 Hb
    iintro Hb
    ihave Hrd := Hwand $$ Hb
    iunfold keyState
    simp only [if_pos hb]
    iframe Hrd
    iunfold scratchPre
    iframe S0 S4 S8 Hsb
  · simp only [if_neg hb]
    icases H with ⟨O0, Hrd, O12, %p, %cap, %hl', %F', %htrace, O4, O8, S0, S4, S8, Hsb⟩
    icases ParseStr.sbuf_bytes $$ Hsb with ⟨%hp, Hb, Hwand⟩
    iexists 1, p
    isplitr
    · ipureintro; omega
    iframe O0 O4 O8 O12 Hb
    iintro Hb
    ihave Hsb := Hwand $$ Hb
    ihave Hempty := sbuf_clear n maxP hl' live F' p cap bytes $$ Hsb
    iunfold keyState
    simp only [if_neg hb]
    iframe Hrd
    iexists p, cap, hl', F'
    isplitr
    · ipureintro; exact htrace
    iunfold scratchPre
    iframe S0 S4 S8 Hempty

set_option maxRecDepth 100000 in
/-- General successful keys at the existing 193/646 boundary, with changing scratch state.
The additional 32 stack bytes travel in the abstract pre/post resources. -/
theorem f646_key (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp de ptr idx ptrS capS : UInt32)
    (ob bs : List UInt8) (q maxP hl F : Nat) (live : List (Nat × Nat)) (key : String) (rest : List UInt8)
    (hob : ob.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 208 ≤ sp.toNat) (hq : q ≤ bs.length)
    (hcap : capS.toNat < 2 ^ 25) (hroom : roomRun maxP hl capS [] (bs.drop q))
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    code646 n maxP inst mi A ⊢
      SerdeNextKey.Spec646 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs q key.toUTF8.toList
        iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP hl live F ptrS capS [])
        (keyCost cfg F capS bs key.toUTF8.toList rest q)
        iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hsc : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  have s := ParseStrSuccess.f646_success_growth_traced (GF := GF) cfg lim d types[31]! rfl
    inst mi A n g ta hm hd Cg gt (sp - 16) (sp - 16) de (de + 12) ptr idx ptrS capS ob bs q
    maxP hl live F hob (by omega) hlen (by omega) (by omega) (by omega) (by omega)
    hq hcap hroom key.toUTF8.toList rest hok hu
  rw [show (sp - 16).toNat - 192 = sp.toNat - 208 by omega] at s
  apply s.trans
  unfold SerdeNextKey.Spec646
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, H160, Ho, Hrd, S8, H32, Hvt, Htables, S0, S4, Hsb⟩
    iunfold SerdeValueState.tables at Htables
    icases Htables with ⟨He, Hw, Hhex⟩
    ihave H192 := stk_join n (sp.toNat - 208) 32 160 $$ [H32 H160]
    · rw [show sp.toNat - 208 + 32 = sp.toNat - 176 by omega]
      iframe H32 H160
    simp only [hsc, Nat.add_assoc, show 12 + 4 = 16 from rfl, show 12 + 8 = 20 from rfl]
    iframe Hg H192 Hvt Ho Hrd S0 S4 S8 Hsb He Hw Hhex
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, H192, Hvt, He, Hw, Hhex, HR⟩
    icases stk_split n (sp.toNat - 208) 32 160 $$ H192 with ⟨H32, H160⟩
    rw [show sp.toNat - 208 + 32 = sp.toNat - 176 by omega]
    iframe Hg H160
    isplitr
    · ipureintro; exact hrs
    icases result_lend n maxP hl live F (sp - 16) de ptr ptrS capS ob bs key.toUTF8.toList rest q
      hde hq hptr hlen hok hu $$ HR with ⟨%t, %p, %hb, O0, O4, O8, O12, Hb, Hwand⟩
    iexists t, p
    isplitr
    · ipureintro; exact hb
    iframe O0 O4 O8 O12 Hb
    iintro Hb
    ihave Hstate := Hwand $$ Hb
    iframe H32 Hvt Hstate
    iunfold SerdeValueState.tables
    iframe He Hw Hhex

set_option maxRecDepth 100000 in
/-- The actual next-key call accepts every model-decoded key, preserving reusable grown scratch. -/
theorem f193_key_model (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 31 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp acc de ptr idx ptrS capS sl : UInt32)
    (bs : List UInt8) (first : Bool) (i q maxP hl F : Nat) (live : List (Nat × Nat))
    (key : String) (rest : List UInt8)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hacc : acc.toNat + 8 ≤ 2 ^ 32) (hsp : 208 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hq : q ≤ bs.length) (hkey : SerdeNextKey.keyQ first bs i = some q)
    (hcap : capS.toNat < 2 ^ 25) (hroom : roomRun maxP hl capS [] (bs.drop q))
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    SerdeNextKey.code193 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[11]! inst mi f193 Cg
        (fun args => iprop(⌜args = [.i32 acc]⌝ ∗ n ↦[i32][ acc.toNat ] de ∗
          n ↦[wms][ acc.toNat + 4 ] [if first then 1 else 0] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 208) 208 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          rd n de ptr bs i ∗ scratchPre n maxP hl live F de ptrS capS sl ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost +
          keyCost cfg F capS bs key.toUTF8.toList rest q)
        (fun _ rs => iprop(⌜rs = [.i64 (SerdeNextKey.fieldOf key.toUTF8.toList)]⌝ ∗
          n ↦[i32][ acc.toNat ] de ∗ n ↦[wms][ acc.toNat + 4 ] [0] ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 208) 208 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
          keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hsc : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  let P : IProp GF := iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗
    SerdeValueState.tables n ∗ n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
    sbuf n maxP hl live F ptrS capS [])
  let Q : IProp GF := iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗
    SerdeValueState.tables n ∗ keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q)
  iintro ⟨#C193, #C646⟩
  have keySpec (ob : List UInt8) (hob : ob.length = 16) :=
    f646_key (GF := GF) cfg lim (d + 1) inst mi A n g ta hm (by omega) Cg gt sp de ptr idx ptrS capS
      ob bs q maxP hl F live key rest hob hlen hptr hde hsp hq hcap hroom hmodel
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hacc, Hfirst, Hg, H208, Hvt, Htables, Hrd, Hscratch, Hkey⟩
  iunfold scratchPre at Hscratch
  icases Hscratch with ⟨S8, S0, S4, Hsb⟩
  icases stk_split n (sp.toNat - 208) 32 176 $$ H208 with ⟨H32, H176⟩
  rw [show sp.toNat - 208 + 32 = sp.toNat - 176 by omega]
  icases stk_split n (sp.toNat - 176) 160 16 $$ H176 with ⟨H160, Hob⟩
  rw [show sp.toNat - 176 + 160 = (sp - 16).toNat by omega]
  iunfold stk at Hob
  icases Hob with ⟨%ob, %hob, Hob⟩
  ihave #S646 := keySpec ob hob $$ C646
  have s := SerdeNextKey.f193_key (GF := GF) cfg lim d types[11]! rfl inst mi A n g ta hm (by omega)
    Cg gt sp acc de ptr first ob bs key.toUTF8.toList i q sl maxP hob (by omega) hptr hde hacc
    (by omega) hi hkey P (keyCost cfg F capS bs key.toUTF8.toList rest q) Q
  ihave #S := s $$ [C193 S646]
  · iframe C193 S646
  iunfold MFunSpec at S
  ihave Hrun := S $$ %args %R [Hacc Hfirst Hg H160 Hob Hrd S8 H32 Hvt Htables S0 S4 Hsb Hkey] Hc
  · simp only [hsc, Nat.add_assoc, show 12 + 8 = 20 from rfl]
    iframe Hacc Hfirst Hg H160 Hob Hrd S8 Hkey
    isplitr
    · ipureintro; exact ha
    dsimp only [P]
    iframe H32 Hvt Htables S0 S4 Hsb
  iapply mwpInvoke_wand
  isplitl [Hrun]
  · iexact Hrun
  isplit
  · iintro %rs ⟨Hc, %hrs, Hacc, Hfirst, Hg, H176, Hkey, HQ⟩
    iunfold Q at HQ
    icases HQ with ⟨H32, Hvt, Htables, Hstate⟩
    ihave H208 := stk_join n (sp.toNat - 208) 32 176 $$ [H32 H176]
    · rw [show sp.toNat - 208 + 32 = sp.toNat - 176 by omega]
      iframe H32 H176
    dsimp only
    iframe Hc Hacc Hfirst Hg H208 Hvt Htables Hkey Hstate
    ipureintro; exact hrs
  · iintro Htrap; iexact Htrap

end Resource
end WNear.Binary.SerdeKeyEsc
