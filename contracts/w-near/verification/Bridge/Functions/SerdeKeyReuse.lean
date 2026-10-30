import Bridge.Functions.SerdeValueReuse

/-!
# Borrowed and copied object keys with reusable scratch

Borrowed keys use the existing no-escape reader, framing any scratch allocated
by earlier members. Copied keys retain the general successful growth charge.
-/

namespace WNear.Binary.SerdeKeyReuse

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (strRun borrowed plain roomRun code646)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (sbuf)
open WNear.Binary.SerdeValueState (scratchPre)
open WNear.Binary.SerdeKeyEsc (keyState)

/-- Use the tight no-escape charge on borrowed keys, and the growth-aware charge otherwise. -/
def keyCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (q : Nat) : Nat :=
  if borrowed (bs.drop q) then ParseStr.cost646 cfg F q bytes (0x22 :: rest)
  else SerdeKeyEsc.keyCost cfg F cap bs bytes rest q

/-- Borrowed keys need no hypothetical scratch append; copied keys retain the general room premise. -/
def keyRoom (maxP hl : Nat) (cap : UInt32) (l : List UInt8) : Prop :=
  if borrowed l then SerdeErrBox.roomFor4 hl maxP 20 else roomRun maxP hl cap [] l

/-- The earlier general room premise still suffices for either path. -/
theorem keyRoom_of_roomRun (maxP hl : Nat) (cap : UInt32) (l : List UInt8)
    (h : roomRun maxP hl cap [] l) : keyRoom maxP hl cap l := by
  unfold keyRoom
  split
  · exact ((ParseStr.roomRun_unfold maxP hl cap [] l).mp h).1
  · exact h

/-- Borrowed keys retain the existing `300 + 130` per consumed byte allowance. -/
theorem keyCost_borrowed (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (q : Nat)
    (hb : borrowed (bs.drop q)) (hok : strRun (bs.drop q) [] = .ok bytes rest)
    (hu : Utf8.utf8Ok bytes = true) :
    keyCost cfg F cap bs bytes rest q =
      (300 + 130 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost := by
  have hs := SerdeKeyEsc.borrowed_split _ _ _ hb hok
  have hl := congrArg List.length hs
  simp only [List.length_append, List.length_cons] at hl
  have hcons : (bs.drop q).length - rest.length = bytes.length + 1 := by omega
  have hsuccess : ParseStr.ok646 bytes (0x22 :: rest) := ⟨rfl, hu⟩
  simp only [keyCost, if_pos hb, ParseStr.cost646, if_pos hsuccess, Nat.add_zero, hcons, FromUtf8.cost927]
  congr 1
  omega

/-- Selecting the borrowed fast path never increases the previous general key allowance. -/
theorem keyCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (q : Nat)
    (hok : strRun (bs.drop q) [] = .ok bytes rest) (hu : Utf8.utf8Ok bytes = true) :
    keyCost cfg F cap bs bytes rest q ≤ SerdeKeyEsc.keyCost cfg F cap bs bytes rest q := by
  by_cases hb : borrowed (bs.drop q)
  · rw [keyCost_borrowed cfg F cap bs bytes rest q hb hok hu]
    unfold SerdeKeyEsc.keyCost
    calc
      _ ≤ (500 + 470 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := Nat.le_add_right _ _
  · simp only [keyCost, if_neg hb, le_refl]

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- A borrowed key preserves previously allocated scratch at the tight no-escape charge. -/
theorem f646_key_borrowed (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp de ptr idx ptrS capS : UInt32)
    (ob bs : List UInt8) (q maxP hl F : Nat) (live : List (Nat × Nat)) (key : String) (rest : List UInt8)
    (hob : ob.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 208 ≤ sp.toNat) (hq : q ≤ bs.length)
    (hr : SerdeErrBox.roomFor4 hl maxP 20) (hb : borrowed (bs.drop q))
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    code646 n maxP inst mi A ⊢
      SerdeNextKey.Spec646 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs q key.toUTF8.toList
        iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP hl live F ptrS capS [])
        (ParseStr.cost646 cfg F q key.toUTF8.toList (0x22 :: rest))
        iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q) := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  obtain ⟨hsplit, hplain, _⟩ := SerdeValueReuse.borrowed_parts _ _ _ hb hok
  have hstop : ∀ x tail, (0x22 :: rest) = x :: tail → plain x = false ∧ x ≠ 0x5C := by
    intro x tail he
    cases he
    decide
  have hend : q + key.toUTF8.toList.length + 1 = bs.length - rest.length := by
    have hs := congrArg List.length hsplit
    simp only [List.length_drop, List.length_append, List.length_cons] at hs
    omega
  have hsc : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have s := SerdeNextKey.f646_key_noesc (GF := GF) cfg lim d inst mi A n g ta hm hd Cg gt sp de ptr idx
    ob bs key.toUTF8.toList (0x22 :: rest) q maxP hl
    (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) F hob (by omega) hptr hde
    (by omega) hq hsplit hplain hstop ⟨rfl, hu⟩ hr
  iintro #HC
  iunfold code646 at HC
  icases HC with ⟨#Herr, -, #F927, #F657, #F647, #F648, -⟩
  ihave #S := s $$ [Herr F927 F657 F647 F648]
  · iframe Herr F927 F657 F647 F648
  clear s
  iunfold SerdeNextKey.Spec646 at S
  iunfold SerdeNextKey.Spec646
  iunfold MFunSpec at S
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, Hg, H160, Ho, Hrd, S8, H32, Hvt, Htables, S0, S4, Hsb⟩
  icases ParseEscape.sbuf_split $$ Hsb with ⟨Hheap, Hscratch⟩
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨He, Hw, Hhex⟩
  iapply mwpInvoke_wand
  isplitl [Hg H160 Ho Hrd S8 Hvt Hheap He Hw Hc]
  · iapply S $$ %args %R [Hg H160 Ho Hrd S8 Hvt Hheap He Hw] Hc
    dsimp only
    iframe Hg H160 Ho Hrd S8 Hvt Hheap He Hw
    ipureintro; exact ha
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %hrs, Hg, H160, %t, %p, %hp, O0, O4, O8, O12, Hb, Hwand⟩
    iframe Hc Hg H160
    isplitr
    · ipureintro; exact hrs
    iexists t, p
    isplitr
    · ipureintro; exact hp
    iframe O0 O4 O8 O12 Hb
    iintro Hb
    icases Hwand $$ Hb with ⟨Hvt, Hheap, He, Hw, S8, Hrd⟩
    rw [hend, hsc, show de.toNat + 12 + 8 = de.toNat + 20 by omega]
    iframe H32 Hvt
    isplitl [He Hw Hhex]
    · iunfold SerdeValueState.tables
      iframe He Hw Hhex
    iunfold keyState
    simp only [if_pos hb]
    iframe Hrd
    iunfold scratchPre
    iframe S8 S0 S4
    iapply ParseEscape.sbuf_join
    iframe Hheap Hscratch
  · iintro Htrap; iexact Htrap


set_option maxRecDepth 100000 in
/-- Every decoded key at a charge selected by its actual borrowed/copied path. -/
theorem f646_key (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 30 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp de ptr idx ptrS capS : UInt32)
    (ob bs : List UInt8) (q maxP hl F : Nat) (live : List (Nat × Nat)) (key : String) (rest : List UInt8)
    (hob : ob.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 208 ≤ sp.toNat) (hq : q ≤ bs.length)
    (hcap : capS.toNat < 2 ^ 25) (hroom : keyRoom maxP hl capS (bs.drop q))
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    code646 n maxP inst mi A ⊢
      SerdeNextKey.Spec646 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs q key.toUTF8.toList
        iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP hl live F ptrS capS [])
        (keyCost cfg F capS bs key.toUTF8.toList rest q)
        iprop(stk n (sp.toNat - 208) 32 ∗ vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          keyState n maxP hl live F de ptr ptrS capS bs key.toUTF8.toList rest q) := by
  by_cases hb : borrowed (bs.drop q)
  · simp only [keyCost, if_pos hb]
    have hr : SerdeErrBox.roomFor4 hl maxP 20 := by simpa only [keyRoom, if_pos hb] using hroom
    exact f646_key_borrowed cfg lim d inst mi A n g ta hm (by omega) Cg gt sp de ptr idx ptrS capS
      ob bs q maxP hl F live key rest hob hlen hptr hde hsp hq hr hb hmodel
  · have hr : roomRun maxP hl capS [] (bs.drop q) := by simpa only [keyRoom, if_neg hb] using hroom
    simpa only [keyCost, if_neg hb] using
      (SerdeKeyEsc.f646_key (GF := GF) cfg lim d inst mi A n g ta hm hd Cg gt sp de ptr idx ptrS capS
        ob bs q maxP hl F live key rest hob hlen hptr hde hsp hq hcap hr hmodel)

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
    (hcap : capS.toNat < 2 ^ 25) (hroom : keyRoom maxP hl capS (bs.drop q))
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
end WNear.Binary.SerdeKeyReuse
