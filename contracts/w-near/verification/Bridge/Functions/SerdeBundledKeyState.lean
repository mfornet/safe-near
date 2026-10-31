import Bridge.Functions.SerdeFieldPrecise
import Bridge.Functions.SerdeStructObjPhaseReaders
import Bridge.Functions.SerdePrefixBounds
import Bridge.Functions.SerdePrefixTrace

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

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def BundledKeyConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B (.member first) i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.keyRoom maxP hl cap (bs.drop q) ∧ SerdeKeyReuse.preciseCost cfg F cap bs key.toUTF8.toList rest q +
      SerdeKeyTight.fieldCost key.toUTF8.toList * cfg.regularOpCost ≤ SerdeKey.cost194 * cfg.regularOpCost + K q ∧
    (∀ hl', hl ≤ hl' → hl' ≤ hl + growthPages cap 0 (appendChunks (bs.drop q) []) * 65536 →
      B (.value key) (bs.length - rest.length) hl' (endFreeBound F cap 0 (appendChunks (bs.drop q) []))
        (endState cap 0 (appendChunks (bs.drop q) [])).1)

set_option maxRecDepth 100000 in
/-- The concrete general key reader discharges the loop's key-call hypothesis from pure bounds. -/
theorem keyHyp_bundled (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : PhaseBounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hc : BundledKeyConditions cfg maxP bs B K) (hcSaved : BundledKeyConditions cfg maxP bs Bsaved K) (Cd : IProp GF) [Persistent Cd]
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
  have hc' : BundledKeyConditions cfg maxP bs C K := by
    rcases hC with rfl | rfl
    · exact hc
    · exact hcSaved
  icases scratch_alignment n maxP hl lv F de ptrS capS sl $$ Hscratch with ⟨%⟨halign, hpositive⟩, Hscratch⟩
  obtain ⟨hr, hcost, hstep⟩ := hc' first i q key rest hl F capS hi hq hmodel hb hcap halign hpositive
  have callKey := SerdeKeyReuse.f193_key_model_precise_field (GF := GF) cfg lim d inst mi A n g ta hm (by omega) Cg gt
    s (s + 32) de ptr idx ptrS capS sl bs first i q maxP hl F lv key rest hlen hptr hde
    (by rw [hs32]; omega) (by omega) hi hql hq hcap hr hmodel
  rw [hs32, show s.toNat + 32 + 4 = s.toNat + 36 by omega] at callKey
  ihave #S := callKey $$ [C193 C646]
  · iframe C193 C646
  clear callKey
  iunfold MFunSpec at S
  ihave Hc := credits_mono (C := Cg)
    (show (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKeyTight.fieldCost key.toUTF8.toList) * cfg.regularOpCost +
      SerdeKeyReuse.preciseCost cfg F capS bs key.toUTF8.toList rest q + R ≤
      (572 + 96 * SerdeNextKey.keyWs first bs i + SerdeKey.cost194) * cfg.regularOpCost + K q + R by simp only [Nat.add_mul]; omega) $$ Hc
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


end Resource
end WNear.Binary.SerdeStructObjPhaseReaders
namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeStructObjPhaseReaders (PhaseBounds)

def BundledKeyGasCharges (cfg : WasmConfig) (bs : List UInt8) (B : PhaseBounds) (K : Nat → Nat) : Prop :=
  ∀ first i q key rest hl F cap, i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    stringBody (bs.drop q) [] = some (some key, rest) →
    B (.member first) i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.preciseCost cfg F cap bs key.toUTF8.toList rest q +
      SerdeKeyTight.fieldCost key.toUTF8.toList * cfg.regularOpCost ≤ SerdeKey.cost194 * cfg.regularOpCost + K q

theorem Bound.bundled_key_conditions (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) (K : Nat → Nat) (hlen : bs.length ≤ 4194304)
    (hbase : baseHL + 18230154 ≤ 100663296)
    (hgas : BundledKeyGasCharges cfg bs (Bound bs start baseHL baseF saved) K) :
    SerdeStructObjPhaseReaders.BundledKeyConditions cfg 2048 bs (Bound bs start baseHL baseF saved) K := by
  intro first i q key rest hl F cap hi hq hm hb hc hal hp
  refine ⟨Ledger.key_room bs baseHL baseF i hl F q saved cap key rest hlen hbase hb.forget hal hp hm,
    hgas first i q key rest hl F cap hi hq hm hb hc hal hp, ?_⟩
  intro hl' hlo hhi
  exact Bound.segment bs start baseHL baseF i (bs.length - rest.length) hl F hl' saved saved
    (.member first) (.value key) cap (.append (ParseStrSuccess.appendChunks (bs.drop q) [])) 0
    (by omega) (fun pre hpre => .key hpre hq hm) hb hlo (by simpa only [Segment.pages, Nat.add_zero, Nat.mul_comm] using hhi)
noncomputable def selectedBundledKeyCost (cfg : WasmConfig) (bs : List UInt8) (start baseF q : Nat) : Nat := by
  classical
  exact
    if h : Nonempty (KeyWitness bs start q) then
      let w := Classical.choice h
      SerdeKeyReuse.bundledCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history)
        bs w.key.toUTF8.toList w.rest q
    else 0

theorem selectedBundledKeyCost_of_witness (cfg : WasmConfig) (bs : List UInt8) (start baseF q : Nat)
    (w : KeyWitness bs start q) :
    SerdeKeyReuse.bundledCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history)
      bs w.key.toUTF8.toList w.rest q = selectedBundledKeyCost cfg bs start baseF q := by
  classical
  unfold selectedBundledKeyCost
  rw [dif_pos ⟨w⟩]
  let other := Classical.choice (show Nonempty (KeyWitness bs start q) from ⟨w⟩)
  change _ = SerdeKeyReuse.bundledCost cfg (endFreeBound baseF 0 other.history) (endCap 0 other.history)
    bs other.key.toUTF8.toList other.rest q
  have hhistory := w.prefixModel.key_history_unique other.prefixModel w.quote other.quote w.model other.model
  have hmodel := Option.some.inj (w.model.symm.trans other.model)
  have hkey := Option.some.inj (congrArg Prod.fst hmodel)
  have hrest := congrArg Prod.snd hmodel
  dsimp only at hrest
  rw [hhistory.1, hkey, hrest]


theorem Bound.selected_bundled_key_charges (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) : BundledKeyGasCharges cfg bs (Bound bs start baseHL baseF saved)
      (selectedBundledKeyCost cfg bs start baseF) := by
  intro first i q key rest hl F cap hi hq hs hb hc hal hp
  obtain ⟨pre, hprefix, hcap, hfree, hlo, hhi⟩ := hb
  subst cap F
  have heq := selectedBundledKeyCost_of_witness cfg bs start baseF q
    ⟨first, i, key, rest, pre, saved, hprefix, hq, hs⟩
  have hf := SerdeKeyReuse.bundledCost_funds_reader_and_field cfg
    (endFreeBound baseF 0 pre) (endCap 0 pre) bs key.toUTF8.toList rest q
  rw [heq] at hf
  exact hf

end WNear.Binary.SerdeObjectPrefix
