import Bridge.Functions.SerdeStructObjPhase
import Bridge.Functions.SerdeObjectKeyPrecise
import Bridge.Functions.SerdeStructObjValueState
import Bridge.Functions.SerdeIgnObjectV86

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeStructObjPhaseReaders

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStr (strRun borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

open WNear.Binary.SerdeStructObjKeyState (Bounds core key_exact scratch_alignment)
open WNear.Binary.SerdeStructObjPhase (Phase)

abbrev PhaseBounds := Phase → Bounds

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The saved String's bytes and allocation stay live through every later key. -/
def member (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (B Bsaved : PhaseBounds) (phase : Phase) (i : Nat) : Option (WNear.AccountId × UInt32 × UInt32) → IProp GF
  | none => core n maxP ta alloc idx de live (B phase) i
  | some (a, p, cap) => iprop(⌜cap = UInt32.ofNat a.val.utf8ByteSize ∧ p ≠ 0⌝ ∗
      n ↦[wms][ p.toNat ] a.val.toUTF8.toList ∗
      core n maxP ta alloc idx de ((p.toNat, cap.toNat) :: live) (Bsaved phase) i)

/-- A saved descriptor lends the parser state and accepts it back at a later reader cursor. -/
theorem seen_core (n maxP ta alloc : Nat) (idx de s : UInt32) (live : List (Nat × Nat))
    (B Bsaved : PhaseBounds) (phase : Phase) (i : Nat) (seen : Option WNear.AccountId) :
    SerdeStructObjPhase.seenRes (GF := GF) n s (member n maxP ta alloc idx de live B Bsaved phase) i seen ⊢
      ∃ (C : PhaseBounds) (lv : List (Nat × Nat)), ⌜C = B ∨ C = Bsaved⌝ ∗ core n maxP ta alloc idx de lv (C phase) i ∗
        (∀ next j, core n maxP ta alloc idx de lv (C next) j -∗
          SerdeStructObjPhase.seenRes n s (member n maxP ta alloc idx de live B Bsaved next) j seen) := by
  iintro H
  cases seen with
  | none =>
    iunfold SerdeStructObjPhase.seenRes at H
    icases H with ⟨%b8, %hb8, S40, S44, Hcore⟩
    iexists B, live
    isplitr
    · ipureintro; exact Or.inl rfl
    dsimp only [member]
    iframe Hcore
    iintro %next %j Hcore
    iunfold SerdeStructObjPhase.seenRes
    iexists b8
    dsimp only [member]
    iframe S40 S44 Hcore
    ipureintro; exact hb8
  | some a =>
    iunfold SerdeStructObjPhase.seenRes at H
    icases H with ⟨%p, %cap, %hp, S40, S44, S48, Hmember⟩
    iunfold member at Hmember
    icases Hmember with ⟨%hv, Hb, Hcore⟩
    iexists Bsaved, (p.toNat, cap.toNat) :: live
    isplitr
    · ipureintro; exact Or.inr rfl
    iframe Hcore
    iintro %next %j Hcore
    iunfold SerdeStructObjPhase.seenRes
    iexists p, cap
    isplitr
    · ipureintro; exact hp
    iframe S40 S44 S48
    iunfold member
    dsimp only
    iframe Hb Hcore
    ipureintro; exact hv

def KeyConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B (.member first) i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.keyRoom maxP hl cap (bs.drop q) ∧ SerdeKeyReuse.preciseCost cfg F cap bs key.toUTF8.toList rest q ≤ K q ∧
    (∀ hl', hl ≤ hl' → hl' ≤ hl + growthPages cap 0 (appendChunks (bs.drop q) []) * 65536 →
      B (.value key) (bs.length - rest.length) hl' (endFreeBound F cap 0 (appendChunks (bs.drop q) []))
        (endState cap 0 (appendChunks (bs.drop q) [])).1)

set_option maxRecDepth 100000 in
/-- The concrete general key reader discharges the loop's key-call hypothesis from pure bounds. -/
theorem keyHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : PhaseBounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hc : KeyConditions cfg maxP bs B K) (hcSaved : KeyConditions cfg maxP bs Bsaved K) (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A) :
    SerdeStructObjPhase.KeyHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs K
      (member n maxP ta (A 578) idx de live B Bsaved) Cd := by
  intro d s first i q key rest seen hd hsp hsend hi hq hmodel
  have hql := SerdeStructObj.keyQ_le hq
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  have hs32 : (s + 32).toNat = s.toNat + 32 := by simp [UInt32.toNat_add]; omega
  iintro #HCd
  ihave Hcode := hcode $$ HCd
  icases Hcode with ⟨#C193, #C646⟩
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, M32, M36, Hg, Hstack, Hrd, Hseen⟩
  icases seen_core n maxP ta (A 578) idx de s live B Bsaved (.member first) i seen $$ Hseen with ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %ptrS, %capS, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hc' : KeyConditions cfg maxP bs C K := by
    rcases hC with rfl | rfl
    · exact hc
    · exact hcSaved
  icases scratch_alignment n maxP hl lv F de ptrS capS sl $$ Hscratch with ⟨%⟨halign, hpositive⟩, Hscratch⟩
  obtain ⟨hr, hcost, hstep⟩ := hc' first i q key rest hl F capS hi hq hmodel hb hcap halign hpositive
  have callKey := SerdeKeyReuse.f193_key_model_precise (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt
    s (s + 32) de ptr idx ptrS capS sl bs first i q maxP hl F lv key rest hlen hptr hde
    (by rw [hs32]; omega) (by omega) hi hql hq hcap hr hmodel
  rw [hs32, show s.toNat + 32 + 4 = s.toNat + 36 by omega] at callKey
  ihave #S := callKey $$ [C193 C646]
  · iframe C193 C646
  clear callKey
  iunfold MFunSpec at S
  ihave Hc := credits_mono (C := Cg)
    (show (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost +
      SerdeKeyReuse.preciseCost cfg F capS bs key.toUTF8.toList rest q + R ≤
      (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost + K q + R by omega) $$ Hc
  icases VecFromElem.stk_split n (s.toNat - 304) 96 208 $$ Hstack with ⟨H96, H208⟩
  rw [show s.toNat - 304 + 96 = s.toNat - 208 by omega]
  iapply mwpInvoke_wand
  isplitl [M32 M36 Hg H208 Hrd Hvt Htables Hkey Hscratch Hc]
  · iapply S $$ %args %R [M32 M36 Hg H208 Hrd Hvt Htables Hkey Hscratch] Hc
    dsimp only
    iframe M32 M36 Hg H208 Hvt Htables Hkey Hscratch Hrd
    ipureintro; exact ha
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %hrs, M32, M36, Hg, H208, Hvt, Htables, Hkey, Hresult⟩
    icases key_exact n maxP hl lv F de ptr ptrS capS bs key.toUTF8.toList rest q hok $$ Hresult with
      ⟨%p', %cap', %sl', %hl', %⟨hcapEq, hlo, hhi⟩, Hrd, Hscratch⟩
    have hcap' : cap'.toNat < 2 ^ 25 := hcapEq ▸ SerdeObjectState.parsed_capacity bs key.toUTF8.toList rest q capS hlen hcap hok
    have hb' : C (.value key) (bs.length - rest.length) hl' (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) cap' :=
      hcapEq ▸ hstep hl' hlo hhi
    iframe Hc M32 M36 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H96 H208]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 96 208
      rw [show s.toNat - 304 + 96 = s.toNat - 208 by omega]
      iframe H96 H208
    iapply Hsaved $$ %(.value key) %(bs.length - rest.length)
    iunfold core
    iexists hl', endFreeBound F capS 0 (appendChunks (bs.drop q) []), p', cap', sl'
    iframe Hvt Htables Hkey Hident Hscratch
    ipureintro; exact ⟨hb', hcap'⟩
  · iintro Htrap; iexact Htrap

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeIgnExecution

/-- All remaining value obligations are pure reachable-state room, charge and endpoint bounds. -/
def ValueConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B Bsaved : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ (i j : Nat) (a : WNear.AccountId) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) →
    bs[j]? = some 0x22 → stringBody (bs.drop (j + 1)) [] = some (some a.val, rest) →
    valueAs WNear.account (bs.drop (i + wsLen (bs.drop i) + 1)) = some (a, rest) →
    B (.value "account_id") i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeErrBox.roomFor4 hl maxP 20 ∧ ParseStr.roomRun maxP hl cap [] (bs.drop (j + 1)) ∧
    roomFor (hl + growthPages cap 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat a.val.toUTF8.toList.length) ∧
    SerdeValueReuse.valueCost cfg F cap bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j ≤
      K (i + wsLen (bs.drop i) + 1) ∧
    (∀ hl', hl ≤ hl' → hl' ≤ hl + (growthPages cap 0 (appendChunks (bs.drop (j + 1)) []) +
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat a.val.toUTF8.toList.length)) 1).toNat) * 65536 →
      Bsaved (.member false) (bs.length - rest.length) hl' (max (endFreeBound F cap 0 (appendChunks (bs.drop (j + 1)) [])) 1)
        (endState cap 0 (appendChunks (bs.drop (j + 1)) [])).1)

set_option maxRecDepth 100000 in
/-- The concrete colon/value call discharges the loop's value hypothesis from pure bounds. -/
theorem valueHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : PhaseBounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hc : ValueConditions cfg maxP bs B Bsaved K) (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A) :
    SerdeStructObjPhase.ValueHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs
      (valueAs WNear.account) K (member n maxP ta (A 578) idx de live B Bsaved) Cd := by
  intro d s ob i a rest hd hsp hsend hob hi hcolon hmodel
  obtain ⟨j, hj, hq, hstr⟩ := SerdeStructObjValueState.account_model hmodel
  have hs32 : (s + 32).toNat = s.toNat + 32 := by simp [UInt32.toNat_add]; omega
  have hvalid : validAccountIdBytes a.val.toUTF8.toList = true := a.toNear.property
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hstr
  have hsize := SerdeDeStrEsc.strRun_size (bs.drop (j + 1)) [] a.val.toUTF8.toList rest hok
  simp only [List.length_nil, Nat.zero_add, List.length_drop] at hsize
  iintro #HCd
  ihave Hcode := hcode $$ HCd
  icases Hcode with ⟨#Hend, #F89, #F169, #H169, #H646⟩
  iunfold MFunSpec
  imodintro
  iintro %args %R Hpre Hc
  icases Hpre with ⟨%ha, M32, Hg, Hstack, Ho, Hrd, Hcore⟩
  iunfold member at Hcore
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %ptrS, %capS, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  icases SerdeStructObjKeyState.scratch_alignment n maxP hl live F de ptrS capS sl $$ Hscratch with
    ⟨%⟨halign, hpositive⟩, Hscratch⟩
  obtain ⟨hr, hroom, halloc, hcost, hstep⟩ := hc i j a rest hl F capS hi hcolon hj hq hstr hmodel hb hcap halign hpositive
  have callValue := SerdeMapValueReuse.f205_model (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt
    s (s + 8) (s + 32) de ptr idx sl ptrS capS ob bs a.val rest i j maxP hl live F hob
    (by simp [UInt32.toNat_add]; omega) hlen hptr hde (by rw [hs32]; omega) (by omega) hi hcolon hj hq
    hcap hstr hr hroom hvalid halloc
  rw [hs32] at callValue
  ihave #S := callValue $$ [Hend F89 F169 H169 H646]
  · iframe Hend F89 F169 H169 H646
  clear callValue
  iunfold MFunSpec at S
  ihave Hc := credits_mono (C := Cg)
    (show (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
      SerdeValueReuse.valueCost cfg F capS bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j + R ≤
      (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + K (i + wsLen (bs.drop i) + 1) + R by omega) $$ Hc
  icases VecFromElem.stk_split n (s.toNat - 304) 16 288 $$ Hstack with ⟨H16, H288⟩
  rw [show s.toNat - 304 + 16 = s.toNat - 288 by omega]
  iapply mwpInvoke_wand
  isplitl [M32 Hg H288 Ho Hrd Hvt Htables Hscratch Hc]
  · iapply S $$ %args %R [M32 Hg H288 Ho Hrd Hvt Htables Hscratch] Hc
    dsimp only
    iframe M32 Hg H288 Ho Hrd Hvt Htables Hscratch
    ipureintro; exact ha
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %hrs, M32, Hg, H288, Hvt, Htables, Hrd, %p, %cap, %len, O0, O4, O8, O12, Hvalue⟩
    iunfold SerdeValueReuse.ownedValue at Hvalue
    icases Hvalue with ⟨%⟨hc, hlenEq, hp⟩, Hb, %scratch, %cap', %sl', %hl', %⟨hcapEq, hlo, hhi⟩, Hscratch⟩
    subst hc hlenEq
    have hcap' : cap'.toNat < 2 ^ 25 := hcapEq ▸ SerdeObjectState.parsed_capacity bs a.val.toUTF8.toList rest (j + 1) capS hlen hcap hok
    have hb' : Bsaved (.member false) (bs.length - rest.length) hl'
        (max (endFreeBound F capS 0 (appendChunks (bs.drop (j + 1)) [])) 1) cap' := hcapEq ▸ hstep hl' hlo hhi
    have hutfLen := Wasm.ByteEncoding.string_utf8_length a.val
    rw [hutfLen]
    iframe Hc M32 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H16 H288]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 16 288
      rw [show s.toNat - 304 + 16 = s.toNat - 288 by omega]
      iframe H16 H288
    iexists p, UInt32.ofNat a.val.utf8ByteSize
    isplitr
    · ipureintro; exact hp
    iframe O0 O4 O8 O12
    iunfold member
    dsimp only
    isplitr
    · ipureintro; exact ⟨rfl, hp⟩
    iframe Hb
    iunfold core
    iexists hl', max (endFreeBound F capS 0 (appendChunks (bs.drop (j + 1)) [])) 1, scratch, cap', sl'
    iframe Hvt Htables Hkey Hident Hscratch
    ipureintro; exact ⟨hb', hcap'⟩
  · iintro Htrap; iexact Htrap

/-- The remaining obligations concern only physically reachable scratch states. Room and final capacity are derived. -/
def IgnoreConditions (cfg : WasmConfig) (bs : List UInt8) (K : Nat → Nat) (B : PhaseBounds) : Prop :=
  ∀ key i hl F cap r ops, key ≠ "account_id" → B (.value key) i hl F cap → cap.toNat < 2 ^ 25 → i ≤ bs.length →
    bs[i + wsLen (bs.drop i)]? = some 0x3A →
    SerdeIgnMachineTrace.trace (bs.drop (i + wsLen (bs.drop i) + 1)) = some (r, ops) →
    hl % 65536 = 0 → 0 < hl →
    hl ≤ 100663296 ∧
    (166 + 470 * (bs.length - r.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg F cap 0 ops ≤ K (i + wsLen (bs.drop i) + 1) ∧
    ∀ hl', HeapTrace hl cap 0 ops hl' →
      B (.member false) (bs.length - r.length) hl' (SerdeIgnTrace.endFreeBound F cap 0 ops) (SerdeIgnTrace.endState cap 0 ops).1


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ignoreHyp_v86 (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : PhaseBounds) (K : Nat → Nat)
    (hlen : bs.length ≤ 4194304) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hconditions : IgnoreConditions cfg bs K B) (hconditionsSaved : IgnoreConditions cfg bs K Bsaved)
    (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeEnds.endCode n 2048 inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n 2048 inst mi A) :
    SerdeStructObjPhase.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs SerdeIgnObject.ignored K
      (member n 2048 ta (A 578) idx de live B Bsaved) Cd := by
  intro d s i rest seen key hkey hd hsp hsend hi hcolon hmodel
  unfold SerdeIgnObject.ignored at hmodel
  simp only [Option.map_eq_some_iff] at hmodel
  obtain ⟨r', hskip, he⟩ := hmodel
  cases he
  obtain ⟨ops, htrace, _, _, _, _⟩ := SerdeIgnMachineTrace.trace_some hskip
  have hs32 : (s + 32).toNat = s.toNat + 32 := by simp [UInt32.toNat_add]; omega
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  iintro #HCd
  ihave Hcode := hcode $$ HCd
  icases Hcode with ⟨#Hend, #F89, #F81, #HC⟩
  iunfold MFunSpec
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%ha, M32, Hg, H304, Hrd, Hseen⟩
  icases seen_core n 2048 ta (A 578) idx de s live B Bsaved (.value key) i seen $$ Hseen with
    ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %p, %cap, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hcond : IgnoreConditions cfg bs K C := by
    rcases hC with rfl | rfl
    · exact hconditions
    · exact hconditionsSaved
  icases SerdeStructObjKeyState.scratch_alignment n 2048 hl lv F de p cap sl $$ Hscratch with
    ⟨%⟨halign, hpositive⟩, Hscratch⟩
  obtain ⟨hceiling, hgas, hbound⟩ := hcond key i hl F cap rest ops hkey hb hcap hi hcolon htrace halign hpositive
  have hendcap := trace_end_cap_v86 (bs.drop (i + wsLen (bs.drop i) + 1)) rest ops cap
    (by simp only [List.length_drop]; omega) hcap htrace
  iunfold SerdeValueState.tables at Htables
  icases Htables with ⟨Hesc, Hwidth, Hhex⟩
  have callIgnore := (f201_traced_v86 (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt s (s + 32) de ptr p cap sl idx
    hl F lv bs rest ops i
    (iprop(n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
    (by omega) hde (by rw [hs32]; omega) hlen hptr hi hcolon (by omega) htrace hpositive halign hceiling).trans
      (AllocGen.MFunSpec_cost (K' := fun _ => (240 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + K (i + wsLen (bs.drop i) + 1))
        (fun _ => by omega))
  rw [hs32] at callIgnore
  ihave #S := callIgnore $$ [Hend F89 F81 HC]
  · iframe Hend F89 F81 HC
  clear callIgnore
  iunfold MFunSpec at S
  icases VecFromElem.stk_split n (s.toNat - 304) 144 160 $$ H304 with ⟨H144, H160⟩
  rw [show s.toNat - 304 + 144 = s.toNat - 160 by omega]
  iapply mwpInvoke_wand
  isplitl [M32 Hg H160 Hvt Hscratch Hrd Hesc Hhex Hident Hwidth Hkey Hc]
  · iapply S $$ %args %R [M32 Hg H160 Hvt Hscratch Hrd Hesc Hhex Hident Hwidth Hkey] Hc
    dsimp only
    iframe M32 Hg H160 Hvt Hscratch Hrd Hesc Hhex Hident Hwidth Hkey
    ipureintro; exact ha
  isplit
  · dsimp only
    iintro %rs ⟨Hc, %p', %hl', %⟨hrs, hheap⟩, M32, Hg, H160, Hvt, Hst, Hrd, Hesc, Hhex, Hident, Hwidth, Hkey⟩
    have hb' := hbound hl' hheap
    iframe Hc M32 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H144 H160]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 144 160
      rw [show s.toNat - 304 + 144 = s.toNat - 160 by omega]
      iframe H144 H160
    iapply Hsaved $$ %(.member false) %(bs.length - rest.length)
    iunfold core
    iexists hl', SerdeIgnTrace.endFreeBound F cap 0 ops, p', (SerdeIgnTrace.endState cap 0 ops).1, 0
    iframe Hvt Hkey Hident
    isplitr
    · ipureintro; exact ⟨hb', hendcap⟩
    isplitl [Hesc Hwidth Hhex]
    · iunfold SerdeValueState.tables
      iframe Hesc Hwidth Hhex
    iunfold SerdeIgnStack.state at Hst
    icases Hst with ⟨D0, D4, D8, Hsb⟩
    iunfold SerdeValueState.scratchPre
    rw [hd12]
    simp only [List.length_nil, List.reverse_nil, Nat.add_assoc, Nat.reduceAdd]
    iframe D8 D0 D4 Hsb
  · iintro Htrap; iexact Htrap

open WNear.Binary.SerdeStructObjModelState (code code_keys code_values)
open WNear.Binary.SerdeIgnObject (ignored ignored_agrees)

def ClosingConditions (bs : List UInt8) (B : PhaseBounds) : Prop :=
  ∀ first i j hl F cap, j = i + wsLen (bs.drop i) → bs[j]? = some 0x7D →
    B (.member first) i hl F cap → B .done (j + 1) hl F cap

theorem member_closing (n maxP ta alloc : Nat) (idx de : UInt32) (live : List (Nat × Nat))
    (bs : List UInt8) (B Bsaved : PhaseBounds) (hB : ClosingConditions bs B)
    (hSaved : ClosingConditions bs Bsaved)
    (first : Bool) (i j : Nat) (seen : Option (WNear.AccountId × UInt32 × UInt32)) (hj : j = i + wsLen (bs.drop i)) (hb : bs[j]? = some 0x7D) :
    member (GF := GF) n maxP ta alloc idx de live B Bsaved (.member first) i seen ⊢ member n maxP ta alloc idx de live B Bsaved .done (j + 1) seen := by
  have hc (C : PhaseBounds) (hC : ClosingConditions bs C)
      (lv : List (Nat × Nat)) : SerdeStructObjKeyState.core (GF := GF) n maxP ta alloc idx de lv (C (.member first)) i ⊢ SerdeStructObjKeyState.core n maxP ta alloc idx de lv (C .done) (j + 1) := by
    iintro H
    iunfold SerdeStructObjKeyState.core at H
    icases H with ⟨%hl, %F, %p, %cap, %sl, %⟨hbound, hcap⟩, Hvt, Htables, Hkey, Hident, Hs⟩
    iunfold SerdeStructObjKeyState.core
    iexists hl, F, p, cap, sl
    iframe Hvt Htables Hkey Hident Hs
    ipureintro; exact ⟨hC first i j hl F cap hj hb hbound, hcap⟩
  cases seen with
  | none => exact hc B hB live
  | some v =>
    obtain ⟨a, p, cap⟩ := v
    iintro H
    iunfold member at H
    icases H with ⟨%hv, Hb, Hcore⟩
    iunfold member
    dsimp only
    iframe Hb
    isplitr
    · ipureintro; exact hv
    iapply hc Bsaved hSaved
    iexact Hcore


set_option maxRecDepth 100000 in
theorem f228_obj_model_closing (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i maxP : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : PhaseBounds) (K646 K169 K81 : Nat → Nat)
    (ign : List UInt8 → Option (Unit × List UInt8)) (hign : Agrees ign valueSkip)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : KeyConditions cfg maxP bs B K646) (hkeysSaved : KeyConditions cfg maxP bs Bsaved K646)
    (hvalues : ValueConditions cfg maxP bs B Bsaved K169)
    (hclose : ClosingConditions bs B)
    (hcloseSaved : ClosingConditions bs Bsaved)
    (hignore : SerdeStructObjPhase.IgnoreHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs ign K81
      (member n maxP ta (A 578) idx de live B Bsaved) iprop(code n maxP inst mi A ∗ Cd))
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ign N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    code n maxP inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n maxP ta (A 578) idx de live B Bsaved (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ign bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n maxP ta (A 578) idx de live B Bsaved .done (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hck : iprop(code n maxP inst mi A ∗ Cd) ⊢
      SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply code_keys n maxP inst mi A
    iexact Hcode
  have hcv : iprop(code n maxP inst mi A ∗ Cd) ⊢
      SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A := by
    iintro ⟨#Hcode, _⟩
    iapply code_values n maxP inst mi A
    iexact Hcode
  have hk := keyHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K646 hlen hptr (by omega) hkeys hkeysSaved iprop(code n maxP inst mi A ∗ Cd) hck
  have hv := valueHyp (GF := GF) cfg lim inst mi A n g ta Cg maxP hm gt idx de ptr
    bs live B Bsaved K169 hlen hptr (by omega) hvalues iprop(code n maxP inst mi A ∗ Cd) hcv
  obtain ⟨_, hdvs, higns, hstrs, _, _⟩ := SerdeFromTrait.reader_facts
    (dv := valueAs WNear.account) (ign := ign) (fun _ => Or.inl rfl) hign bs
  have result := SerdeStructObjPhase.f228_obj_state_closing (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx x2 x3 x4 x5 ob bs i maxP hob hout (by omega) hptr hde hsp hal hi
    (valueAs WNear.account) ign K646 K169 K81 (member n maxP ta (A 578) idx de live B Bsaved)
    iprop(code n maxP inst mi A ∗ Cd) hk hv hignore
    (fun first i j seen hj hb => member_closing n maxP ta (A 578) idx de live bs B Bsaved hclose hcloseSaved first i j seen hj hb)
    hdvs higns hstrs N a rF hb0 hloop
  iintro ⟨#Hcode, #HCd⟩
  iapply result
  iframe Hcode HCd
  iunfold code at Hcode
  icases Hcode with ⟨#C193, -, -, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77⟩
  iframe C193 F205 F201 F193 F89 F90 F81 F169 F77
set_option maxRecDepth 100000 in
theorem object_loop_v86_closing (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 42 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (live : List (Nat × Nat)) (Cd : IProp GF) [Persistent Cd] (B Bsaved : PhaseBounds) (K646 K169 K81 : Nat → Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length ≤ 4194304)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 368 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hi : i ≤ bs.length)
    (hkeys : KeyConditions cfg 2048 bs B K646) (hkeysSaved : KeyConditions cfg 2048 bs Bsaved K646)
    (hvalues : ValueConditions cfg 2048 bs B Bsaved K169)
    (hclose : ClosingConditions bs B)
    (hcloseSaved : ClosingConditions bs Bsaved)
    (hignored : IgnoreConditions cfg bs K81 B)
    (hignoredSaved : IgnoreConditions cfg bs K81 Bsaved)
    (N : Nat) (a : WNear.AccountId) (rF : List UInt8)
    (hb0 : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rF)) :
    SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd) ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗ n ↦[wms][ out.toNat ] ob ∗
          rd n de ptr bs i ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗
          member n 2048 ta (A 578) idx de live B Bsaved (.member true) (i + wsLen (bs.drop i) + 1) none))
        (fun _ => SerdeStructObj.costObj cfg K646 K169 K81 (valueAs WNear.account) ignored bs N i)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 368) 368 ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ ∃ (p cap : UInt32),
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] cap ∗
          n ↦[i32][ out.toNat + 12 ] UInt32.ofNat a.val.utf8ByteSize ∗ ⌜p ≠ 0⌝ ∗
          member n 2048 ta (A 578) idx de live B Bsaved .done (bs.length - rF.length) (some (a, p, cap)) ∗
          rd n de ptr bs (bs.length - rF.length))) := by
  have hcode : iprop(SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd)) ⊢
      SerdeEnds.endCode n 2048 inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
        A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ SerdeIgnMember.code n 2048 inst mi A := by
    iintro ⟨#Hobj, #Hmember, _⟩
    iunfold SerdeStructObjModelState.code at Hobj
    icases Hobj with ⟨#C193, -, -, -, -, -, #F89, -, #F81, -⟩
    iunfold SerdeNextKey.code193 at C193
    icases C193 with ⟨#Cend, -⟩
    iframe Cend F89 F81 Hmember
  have hignore := ignoreHyp_v86 cfg lim inst mi A n g ta Cg hm gt idx de ptr bs live B Bsaved K81 hlen hptr (by omega)
    hignored hignoredSaved iprop(SerdeStructObjModelState.code n 2048 inst mi A ∗ (SerdeIgnMember.code n 2048 inst mi A ∗ Cd)) hcode
  exact f228_obj_model_closing cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out de ptr idx x2 x3 x4 x5
    ob bs i 2048 live iprop(SerdeIgnMember.code n 2048 inst mi A ∗ Cd) B Bsaved K646 K169 K81 ignored ignored_agrees
    hob hout (by omega) hptr hde hsp hal hi hkeys hkeysSaved hvalues hclose hcloseSaved hignore N a rF hb0 hloop
end Resource
end WNear.Binary.SerdeStructObjPhaseReaders
