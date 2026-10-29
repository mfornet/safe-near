import Bridge.Functions.SerdeStructObjKeyState
import Bridge.Functions.SerdeMapValueReuse
import Bridge.Functions.SerdeAcctHyp

/-! # Concrete account-id value reading inside the changing-state object loop -/

namespace WNear.Binary.SerdeStructObjValueState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeStructObjKeyState (Bounds core member)
open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel

/-- An account-id value accepted by the model supplies the quote and decoded string of the actual reader. -/
theorem account_model {bs : List UInt8} {i : Nat} {a : WNear.AccountId} {r : List UInt8}
    (h : valueAs WNear.account (bs.drop i) = some (a, r)) :
    ∃ j, j = i + wsLen (bs.drop i) ∧ bs[j]? = some 0x22 ∧
      stringBody (bs.drop (j + 1)) [] = some (some a.val, r) := by
  unfold valueAs at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨v, r'⟩, hv, a', hacc, rfl, rfl⟩ := h
  unfold WNear.account at hacc
  simp only [Option.map_eq_some_iff] at hacc
  obtain ⟨na, hna, rfl⟩ := hacc
  cases v with
  | str s =>
    simp only [accountId, string, Option.bind_eq_bind, Option.bind_some] at hna
    split at hna
    · rename_i hval
      simp only [Option.some.injEq] at hna
      subst hna
      obtain ⟨rest, hsk, hsb⟩ := SerdeAcctHyp.valueR_str hv
      obtain ⟨hb, hrest⟩ := SerdeStructLoop.skip_drop_cons hsk
      refine ⟨i + wsLen (bs.drop i), rfl, hb, ?_⟩
      rw [← hrest]
      exact hsb
    · simp at hna
  | _ => simp [accountId, string] at hna

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- All remaining value obligations are pure reachable-state room, charge and endpoint bounds. -/
def ValueConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B Bsaved : Bounds) (K : Nat → Nat) : Prop :=
  ∀ (i j : Nat) (a : WNear.AccountId) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → bs[i + wsLen (bs.drop i)]? = some 0x3A →
    j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) →
    bs[j]? = some 0x22 → stringBody (bs.drop (j + 1)) [] = some (some a.val, rest) →
    B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeErrBox.roomFor4 hl maxP 20 ∧ ParseStr.roomRun maxP hl cap [] (bs.drop (j + 1)) ∧
    roomFor (hl + growthPages cap 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat a.val.toUTF8.toList.length) ∧
    SerdeValueReuse.valueCost cfg F cap bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j ≤
      K (i + wsLen (bs.drop i) + 1) ∧
    (∀ hl', hl ≤ hl' → hl' ≤ hl + (growthPages cap 0 (appendChunks (bs.drop (j + 1)) []) +
        (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat a.val.toUTF8.toList.length)) 1).toNat) * 65536 →
      Bsaved (bs.length - rest.length) hl' (max (endFreeBound F cap 0 (appendChunks (bs.drop (j + 1)) [])) 1)
        (endState cap 0 (appendChunks (bs.drop (j + 1)) [])).1)

set_option maxRecDepth 100000 in
/-- The concrete colon/value call discharges the loop's value hypothesis from pure bounds. -/
theorem valueHyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : Bounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hc : ValueConditions cfg maxP bs B Bsaved K) (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeEnds.endCode n maxP inst mi A ∗ A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ SerdeAccountId.code169 n maxP inst mi A ∗
      ParseStr.code646 n maxP inst mi A) :
    SerdeStructObjState.ValueHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs
      (valueAs WNear.account) K (member n maxP ta (A 578) idx de live B Bsaved) Cd := by
  intro d s ob i a rest hd hsp hsend hob hi hcolon hmodel
  obtain ⟨j, hj, hq, hstr⟩ := account_model hmodel
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
  obtain ⟨hr, hroom, halloc, hcost, hstep⟩ := hc i j a rest hl F capS hi hcolon hj hq hstr hb hcap halign hpositive
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
    have hb' : Bsaved (bs.length - rest.length) hl'
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

end Resource
end WNear.Binary.SerdeStructObjValueState
