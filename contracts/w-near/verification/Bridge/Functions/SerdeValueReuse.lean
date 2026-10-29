import Bridge.Functions.SerdeObjectState
import Bridge.Functions.SerdeKeyNoEsc

/-!
# One owned-value boundary for borrowed and copied strings

Plain values may follow escaped keys, so their scratch allocation need not be
empty. Both paths retain the String and return scratch in the layout required
by subsequent object members.
-/

namespace WNear.Binary.SerdeValueReuse

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (plain strRun borrowed)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (sbuf endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre valueStorage)

/-- Successful borrowed parsing identifies both the plain bytes and the empty append trace. -/
theorem borrowed_parts (l bytes rest : List UInt8) (hb : borrowed l)
    (hok : strRun l [] = .ok bytes rest) :
    l = bytes ++ (0x22 :: rest) ∧ (∀ b ∈ bytes, plain b = true) ∧ appendChunks l [] = [] := by
  unfold borrowed at hb
  cases hd : l.dropWhile plain with
  | nil => simp [hd] at hb
  | cons b tail =>
    simp only [hd, List.head?_cons, Option.some.injEq] at hb
    subst b
    rw [ParseStr.strRun_cons _ _ _ _ hd] at hok
    simp only [ite_true, List.nil_append, ParseStr.StrOut.ok.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine ⟨(List.takeWhile_append_dropWhile (p := plain) (l := l)).symm.trans (by rw [hd]),
      fun _ hm => SerdeKeyNoEsc.takeWhile_mem hm, ?_⟩
    rw [ParseStrSuccess.appendChunks_close l [] tail hd]
    simp

/-- The existing accepting charge for either the borrowed or the copied value path. -/
def valueCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (i j : Nat) : Nat :=
  (400 + AccountIdValid.cost554 bytes.length) * cfg.regularOpCost +
    if borrowed (bs.drop (j + 1)) then SerdeDeStr.cost380 cfg F bs bytes (0x22 :: rest) j (wsLen (bs.drop i))
    else SerdeDeStrEsc.costCopied cfg F cap bs bytes rest i j

/-- Both paths fit the existing copied-reader charge; borrowed parsing has no scratch-growth term. -/
theorem valueCost_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs bytes rest : List UInt8) (i j : Nat)
    (hq : j < bs.length) (hok : strRun (bs.drop (j + 1)) [] = .ok bytes rest)
    (hu : Utf8.utf8Ok bytes = true) :
    valueCost cfg F cap bs bytes rest i j ≤ (400 + AccountIdValid.cost554 bytes.length) * cfg.regularOpCost +
      SerdeDeStrEsc.costCopied cfg F cap bs bytes rest i j := by
  by_cases hb : borrowed (bs.drop (j + 1))
  · obtain ⟨hsplit, _, hchunks⟩ := borrowed_parts _ _ _ hb hok
    have hlen := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons] at hlen
    have hcons : (bs.drop (j + 1)).length - rest.length = bytes.length + 1 := by omega
    have h646 : ParseStr.ok646 bytes (0x22 :: rest) := ⟨rfl, hu⟩
    have h380 : SerdeDeStr.ok380 bs bytes (0x22 :: rest) j := ⟨hq, h646⟩
    unfold valueCost SerdeDeStrEsc.costCopied SerdeDeStr.cost380 ParseStr.cost646
    simp only [if_pos hb, if_pos hq, if_pos h380, if_pos h646, hchunks, hcons,
      ScratchGrow.growthCount, ParseStrSuccess.growthBudget, endFreeBound, ite_true,
      FromUtf8.cost927, Nat.add_zero]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one]
    omega
  · simp only [valueCost, if_neg hb]
    exact Nat.le_refl _

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- An owned account-id value with reusable scratch and exact parser/copy growth bounds. -/
def ownedValue (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de capS : UInt32) (bs bytes : List UInt8) (q : Nat) (p c len : UInt32) : IProp GF :=
  iprop(⌜c = UInt32.ofNat bytes.length ∧ len = UInt32.ofNat bytes.length ∧ p ≠ 0⌝ ∗
    n ↦[wms][ p.toNat ] bytes ∗ ∃ (scratch cap sl : UInt32) (hl' : Nat),
      ⌜cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧ hl ≤ hl' ∧
        hl' ≤ hl + (growthPages capS 0 (appendChunks (bs.drop q) []) +
          (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bytes.length)) 1).toNat) * 65536⌝ ∗
      scratchPre n maxP hl' ((p.toNat, c.toNat) :: live)
        (max (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) 1) de scratch cap sl)

/-- A copied value has the common owned-value boundary after forgetting scratch's logical contents. -/
theorem valueStorage_owned (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr capS : UInt32) (bs bytes : List UInt8) (q : Nat) (p c len : UInt32)
    (hbytes : 0 < bytes.length) (hsmall : bytes.length < 2 ^ 32) :
    valueStorage (GF := GF) n maxP hl live F de ptr capS bs bytes q p c len ⊢
      ownedValue n maxP hl live F de capS bs bytes q p c len := by
  iintro H
  ihave H := SerdeObjectState.valueStorage_reuse n maxP hl live F de ptr capS bs bytes q p c len hbytes hsmall $$ H
  icases H with ⟨%hv, Hb, %scratch, %cap, %hl', %ht, Hs⟩
  iunfold ownedValue
  isplitr
  · ipureintro; exact hv
  iframe Hb
  iexists scratch, cap, UInt32.ofNat bytes.length, hl'
  iframe Hs
  ipureintro; exact ht

/-- After allocating the String, rejoin unchanged scratch with the heap in scratch-first order. -/
theorem heapS_reuse (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (scratch cap size p : UInt32) (hs : size ≠ 0) :
    SerdeString.heapS (GF := GF) n maxP hl (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live) F size p ∗
      ParseEscape.sbufR n scratch cap [] ⊢
      ∃ hl', ⌜p ≠ 0 ∧ hl ≤ hl' ∧ hl' ≤ hl +
          (AllocNewCell.cellPages (AllocAlloc.wordsOf size) 1).toNat * 65536⌝ ∗
        sbuf n maxP hl' ((p.toNat, size.toNat) :: live) (max F 1) scratch cap [] := by
  iintro ⟨Hheap, Hscratch⟩
  iunfold SerdeString.heapS at Hheap
  simp only [if_neg hs]
  icases Hheap with ⟨%⟨hp, hpbound⟩, %hl', %hg, Hheap⟩
  have hperm : ((p.toNat, size.toNat) :: (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live)).Perm
      (if cap = 0 then (p.toNat, size.toNat) :: live else (scratch.toNat, cap.toNat) :: (p.toNat, size.toNat) :: live) := by
    split
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _
  ihave Hheap := heapInv_perm n maxP hl' _ _ (max F 1) hperm $$ Hheap
  iexists hl'
  isplitr
  · ipureintro
    unfold grownLen at hg
    rcases hg with he | he <;> exact ⟨hp, by omega, by omega⟩
  iapply ParseEscape.sbuf_join
  iframe Hheap Hscratch

set_option maxRecDepth 100000 in
/-- A plain model-decoded account id is accepted even when earlier keys allocated scratch. -/
theorem f169_borrowed_model (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out de ptr idx ptrS capS sl : UInt32)
    (ob bs : List UInt8) (value : String) (rest : List UInt8) (i j maxP hl F : Nat)
    (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 288 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hq : bs[j]? = some 0x22)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hborrowed : borrowed (bs.drop (j + 1))) (hvalid : validAccountIdBytes value.toUTF8.toList = true)
    (hr : SerdeErrBox.roomFor4 hl maxP 20) (halloc : roomFor hl maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    SerdeAccountId.code169 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[14]! inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 288) 288 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n))
        (fun _ => (400 + AccountIdValid.cost554 value.toUTF8.toList.length) * cfg.regularOpCost +
          SerdeDeStr.cost380 cfg F bs value.toUTF8.toList (0x22 :: rest) j (wsLen (bs.drop i)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 288) 288 ∗
          vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          rd n de ptr bs (bs.length - rest.length) ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len)) := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  obtain ⟨hsplit, hplain, hchunks⟩ := borrowed_parts _ _ _ hborrowed hok
  have hjl := SerdeNextKey.getElem_lt hq
  have hstop : ∀ x tail, (0x22 :: rest) = x :: tail → plain x = false ∧ x ≠ 0x5C := by
    intro x tail he
    cases he
    decide
  have h380 : SerdeDeStr.ok380 bs value.toUTF8.toList (0x22 :: rest) j := ⟨hjl, rfl, hu⟩
  have hsize := SerdeDeStrEsc.strRun_size (bs.drop (j + 1)) [] value.toUTF8.toList rest hok
  simp only [List.length_nil, Nat.zero_add, List.length_drop] at hsize
  have hvalid' := hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid'
  have hsize0 : UInt32.ofNat value.toUTF8.toList.length ≠ 0 := by
    intro he
    have he' := congrArg UInt32.toNat he
    have hm : (UInt32.ofNat value.toUTF8.toList.length).toNat = value.toUTF8.toList.length := by
      change value.toUTF8.toList.length % 2 ^ 32 = value.toUTF8.toList.length
      exact Nat.mod_eq_of_lt (by omega)
    rw [hm] at he'
    change value.toUTF8.toList.length = 0 at he'
    omega
  have hend : j + 1 + value.toUTF8.toList.length + 1 = bs.length - rest.length := by
    have h := congrArg List.length hsplit
    simp only [List.length_drop, List.length_append, List.length_cons] at h
    omega
  have hs := SerdeAccountId.f169_s (GF := GF) cfg lim d types[14]! rfl inst mi A n g ta hm hd Cg gt
    sp out de ptr idx sl ob bs value.toUTF8.toList (0x22 :: rest) i j maxP hl
    (if capS = 0 then live else (ptrS.toNat, capS.toNat) :: live) F hob hout (by omega) hptr hde
    (by omega) hi hj (fun _ => hq) hsplit hplain hstop hr (fun _ => halloc) (fun _ => hvalid)
  apply hs.trans
  apply AllocFresh.MFunSpec_frame
    (Fr := iprop(stk n (sp.toNat - 288) 32 ∗ n ↦[i32][ de.toNat + 12 ] ptrS ∗
      n ↦[i32][ de.toNat + 16 ] capS ∗ ParseEscape.sbufR n ptrS capS [] ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
  · intro args
    iintro ⟨%ha, Hg, H288, Hvt, Ho, Hrd, Hscratch, Htables⟩
    iunfold scratchPre at Hscratch
    icases Hscratch with ⟨S8, S0, S4, Hsb⟩
    icases ParseEscape.sbuf_split $$ Hsb with ⟨Hheap, Hscratch⟩
    iunfold SerdeValueState.tables at Htables
    icases Htables with ⟨He, Hw, Hhex⟩
    icases VecFromElem.stk_split n (sp.toNat - 288) 32 256 $$ H288 with ⟨H32, H256⟩
    rw [show sp.toNat - 288 + 32 = sp.toNat - 256 by omega]
    iframe Hg H256 Hvt Hheap Ho Hrd S8 He Hw H32 S0 S4 Hscratch Hhex
    ipureintro; exact ha
  · intro args rs
    iintro ⟨⟨H32, S0, S4, Hscratch, Hhex⟩, %hrs, Hg, H256, Hvt, ⟨%sl', S8⟩, He, Hw, HR⟩
    iunfold SerdeDeStr.res380 at HR
    simp only [if_pos h380]
    icases HR with ⟨%p, O0, O4, O8, O12, Hheap, Hb, Hrd⟩
    icases heapS_reuse n maxP hl live F ptrS capS (UInt32.ofNat value.toUTF8.toList.length) p hsize0
      $$ [Hheap Hscratch] with ⟨%hl', %⟨hp, hlo, hhi⟩, Hsb⟩
    · iframe Hheap Hscratch
    ihave H288 := VecFromElem.stk_join n (sp.toNat - 288) 32 256 $$ [H32 H256]
    · rw [show sp.toNat - 288 + 32 = sp.toNat - 256 by omega]
      iframe H32 H256
    rw [hend]
    iframe Hg H288 Hvt Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [He Hw Hhex]
    · iunfold SerdeValueState.tables
      iframe He Hw Hhex
    iexists p, UInt32.ofNat value.toUTF8.toList.length, UInt32.ofNat value.toUTF8.toList.length
    iframe O0 O4 O8 O12
    iunfold ownedValue
    simp only [hchunks, endState, endFreeBound, growthPages, Nat.zero_add]
    isplitr
    · ipureintro; exact ⟨True.intro, True.intro, hp⟩
    iframe Hb
    iexists ptrS, capS, sl', hl'
    isplitr
    · ipureintro; exact ⟨rfl, hlo, hhi⟩
    iunfold scratchPre
    iframe S8 S0 S4 Hsb

set_option maxRecDepth 100000 in
/-- Every valid model-decoded account-id string, with arbitrary reusable initial scratch. -/
theorem f169_model (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 33 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out de ptr idx ptrS capS sl : UInt32)
    (ob bs : List UInt8) (value : String) (rest : List UInt8) (i j maxP hl F : Nat)
    (live : List (Nat × Nat))
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 288 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hq : bs[j]? = some 0x22)
    (hcap : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true) (hr : SerdeErrBox.roomFor4 hl maxP 20)
    (hroom : ParseStr.roomRun maxP hl capS [] (bs.drop (j + 1)))
    (halloc : roomFor (hl + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    SerdeAccountId.code169 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d types[14]! inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 288) 288 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n))
        (fun _ => valueCost cfg F capS bs value.toUTF8.toList rest i j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 288) 288 ∗
          vt n 1057464 idx ta (A 578) ∗ SerdeValueState.tables n ∗
          rd n de ptr bs (bs.length - rest.length) ∗ ∃ (p c len : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] len ∗ ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len)) := by
  by_cases hb : borrowed (bs.drop (j + 1))
  · have ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
    have hchunks := (borrowed_parts _ _ _ hb hok).2.2
    have halloc' : roomFor hl maxP (UInt32.ofNat value.toUTF8.toList.length) := by
      simpa only [hchunks, growthPages, Nat.zero_mul, Nat.add_zero] using halloc
    simp only [valueCost, if_pos hb]
    iintro ⟨#H169, _⟩
    iapply f169_borrowed_model cfg lim d inst mi A n g ta hm (by omega) Cg gt sp out de ptr idx ptrS capS sl
      ob bs value rest i j maxP hl F live hob hout hlen hptr hde hsp hi hj hq hmodel hb hvalid hr halloc'
    iexact H169
  · simp only [valueCost, if_neg hb]
    have hv := hvalid
    simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hv
    have hs := SerdeAccountIdEsc.f169_copied_model (GF := GF) cfg lim d types[14]! rfl inst mi A n g ta hm hd Cg gt
      sp out de ptr idx sl ptrS capS ob bs value rest i j maxP hl live F hob hout hlen (by omega) hde hsp hi hj
      (SerdeNextKey.getElem_lt hq) hq hcap hmodel hb hroom hvalid halloc
    apply hs.trans
    apply SerdeValueState.spec_repack
    · intro args
      iintro ⟨%ha, Hg, Hs, Hvt, Ho, Hrd, Hscratch, Htables⟩
      iunfold scratchPre at Hscratch
      icases Hscratch with ⟨S8, S0, S4, Hsb⟩
      iunfold SerdeValueState.tables at Htables
      icases Htables with ⟨He, Hw, Hhex⟩
      iframe Hg Hs Hvt Ho Hrd S8 S0 S4 Hsb He Hw Hhex
      ipureintro; exact ha
    · intro args rs
      iintro ⟨%hrs, Hg, Hs, Hvt, He, Hw, Hhex, HR⟩
      ihave HR := SerdeValueState.copiedResult_split n maxP hl live F out de ptr capS bs value.toUTF8.toList rest (j + 1) $$ HR
      icases HR with ⟨%p, %c, %len, %hp, O0, O4, O8, O12, Hvalue⟩
      icases SerdeValueState.valuePost_split n maxP hl live F de ptr capS bs value.toUTF8.toList rest (j + 1) p c len
        $$ Hvalue with ⟨Hrd, Hstorage⟩
      iframe Hg Hs Hvt Hrd
      isplitr
      · ipureintro; exact hrs
      isplitl [He Hw Hhex]
      · iunfold SerdeValueState.tables
        iframe He Hw Hhex
      iexists p, c, len
      iframe O0 O4 O8 O12
      iapply valueStorage_owned n maxP hl live F de ptr capS bs value.toUTF8.toList (j + 1) p c len (by omega) (by omega)
      iexact Hstorage

/-- Expose the nonzero owned pointer without consuming its reusable scratch state. -/
theorem ownedValue_ne (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de capS : UInt32) (bs bytes : List UInt8) (q : Nat) (p c len : UInt32) :
    ownedValue (GF := GF) n maxP hl live F de capS bs bytes q p c len ⊢
      ⌜p ≠ 0⌝ ∗ ownedValue n maxP hl live F de capS bs bytes q p c len := by
  iintro H
  iunfold ownedValue at H
  icases H with ⟨%hv, Hb, Hs⟩
  isplitr
  · ipureintro; exact hv.2.2
  iunfold ownedValue
  iframe Hb Hs
  ipureintro; exact hv

set_option maxRecDepth 100000 in
/-- The existing sequence-element reader boundary for either successful string path. -/
theorem spec169_model (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 33 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp de ptr idx ptrS capS sl : UInt32)
    (ob bs : List UInt8) (value : String) (rest : List UInt8) (i j maxP hl F : Nat)
    (live : List (Nat × Nat))
    (hob : ob.length = 16) (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 304 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hq : bs[j]? = some 0x22)
    (hcap : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hvalid : validAccountIdBytes value.toUTF8.toList = true) (hr : SerdeErrBox.roomFor4 hl maxP 20)
    (hroom : ParseStr.roomRun maxP hl capS [] (bs.drop (j + 1)))
    (halloc : roomFor (hl + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat value.toUTF8.toList.length)) :
    SerdeAccountId.code169 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A ⊢
      SerdeSeqElem.Spec169 (GF := GF) cfg lim d inst mi n g Cg gt sp de ptr ob bs i
        iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          scratchPre n maxP hl live F de ptrS capS sl ∗ SerdeValueState.tables n)
        (valueCost cfg F capS bs value.toUTF8.toList rest i j)
        (fun p c len => iprop(stk n (sp.toNat - 304) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          SerdeValueState.tables n ∗ rd n de ptr bs (bs.length - rest.length) ∗
          ownedValue n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hs := f169_model (GF := GF) cfg lim d inst mi A n g ta hm hd Cg gt
    (sp - 16) (sp - 16) de ptr idx ptrS capS sl ob bs value rest i j maxP hl F live
    hob (by omega) hlen hptr hde (by omega) hi hj hq hcap hmodel hvalid hr hroom halloc
  rw [show (sp - 16).toNat - 288 = sp.toNat - 304 by omega] at hs
  unfold SerdeSeqElem.Spec169
  apply hs.trans
  apply SerdeValueState.spec_repack
  · intro args
    iintro ⟨%ha, Hg, Ho, Hrd, Hs, Hvt, Hscratch, Htables⟩
    iframe Hg Hs Hvt Ho Hrd Hscratch Htables
    ipureintro; exact ha
  · intro args rs
    iintro ⟨%hrs, Hg, Hs, Hvt, Htables, Hrd, %p, %c, %len, O0, O4, O8, O12, Hvalue⟩
    icases ownedValue_ne n maxP hl live F de capS bs value.toUTF8.toList (j + 1) p c len $$ Hvalue with ⟨%hp, Hvalue⟩
    iframe Hg
    isplitr
    · ipureintro; exact hrs
    iexists p, c, len
    isplitr
    · ipureintro; exact hp
    dsimp only
    iframe O0 O4 O8 O12 Hs Hvt Htables Hrd Hvalue

end Resource
end WNear.Binary.SerdeValueReuse
