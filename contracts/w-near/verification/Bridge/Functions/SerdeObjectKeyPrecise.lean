import Bridge.Functions.SerdeKeyPrecise
import Bridge.Functions.SerdeStructObjKeyState

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeStructObjKeyState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (strRun borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (endState endFreeBound growthPages)
open WNear.Binary.SerdeValueState (scratchPre)

section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]

def PreciseKeyConditions (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8) (B : WNear.Binary.SerdeStructObjKeyState.Bounds) (K : Nat → Nat) : Prop :=
  ∀ (first : Bool) (i q : Nat) (key : String) (rest : List UInt8) (hl F : Nat) (cap : UInt32),
    i ≤ bs.length → SerdeNextKey.keyQ first bs i = some q →
    NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest) → B i hl F cap → cap.toNat < 2 ^ 25 → hl % 65536 = 0 → 0 < hl →
    SerdeKeyReuse.keyRoom maxP hl cap (bs.drop q) ∧ SerdeKeyReuse.preciseCost cfg F cap bs key.toUTF8.toList rest q ≤ K q ∧
    (∀ hl', hl ≤ hl' → hl' ≤ hl + growthPages cap 0 (appendChunks (bs.drop q) []) * 65536 →
      B (bs.length - rest.length) hl' (endFreeBound F cap 0 (appendChunks (bs.drop q) []))
        (endState cap 0 (appendChunks (bs.drop q) [])).1)

set_option maxRecDepth 100000 in
/-- The concrete general key reader discharges the loop's key-call hypothesis from pure bounds. -/
theorem keyHyp_precise (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta Cg maxP : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType) (idx de ptr : UInt32)
    (bs : List UInt8) (live : List (Nat × Nat)) (B Bsaved : Bounds) (K : Nat → Nat)
    (hlen : bs.length < 2 ^ 24) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hc : PreciseKeyConditions cfg maxP bs B K) (hcSaved : PreciseKeyConditions cfg maxP bs Bsaved K) (Cd : IProp GF) [Persistent Cd]
    (hcode : Cd ⊢ SerdeNextKey.code193 n maxP inst mi A ∗ ParseStr.code646 n maxP inst mi A) :
    SerdeStructObjState.KeyHyp (GF := GF) cfg lim inst mi n g Cg gt de ptr bs K
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
  icases seen_core n maxP ta (A 578) idx de s live B Bsaved i seen $$ Hseen with ⟨%C, %lv, %hC, Hcore, Hsaved⟩
  iunfold core at Hcore
  icases Hcore with ⟨%hl, %F, %ptrS, %capS, %sl, %⟨hb, hcap⟩, Hvt, Htables, Hkey, Hident, Hscratch⟩
  have hc' : PreciseKeyConditions cfg maxP bs C K := by
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
    have hb' : C (bs.length - rest.length) hl' (endFreeBound F capS 0 (appendChunks (bs.drop q) [])) cap' :=
      hcapEq ▸ hstep hl' hlo hhi
    iframe Hc M32 M36 Hg Hrd
    isplitr
    · ipureintro; exact hrs
    isplitl [H96 H208]
    · iapply VecFromElem.stk_join n (s.toNat - 304) 96 208
      rw [show s.toNat - 304 + 96 = s.toNat - 208 by omega]
      iframe H96 H208
    iapply Hsaved $$ %(bs.length - rest.length)
    iunfold core
    iexists hl', endFreeBound F capS 0 (appendChunks (bs.drop q) []), p', cap', sl'
    iframe Hvt Htables Hkey Hident Hscratch
    ipureintro; exact ⟨hb', hcap'⟩
  · iintro Htrap; iexact Htrap

end Resource
end WNear.Binary.SerdeStructObjKeyState
namespace WNear.Binary.SerdeStructObjKeyState
open Wasm Wasm.Near WNear.Binary

theorem precise_conditions_of_legacy (cfg : WasmConfig) (maxP : Nat) (bs : List UInt8)
    (B : WNear.Binary.SerdeStructObjKeyState.Bounds) (K : Nat → Nat) (hlen : bs.length < 2 ^ 24) (hc : KeyConditions cfg maxP bs B K) :
    PreciseKeyConditions cfg maxP bs B K := by
  intro first i q key rest hl F cap hi hq hm hb hcap hal hp
  obtain ⟨hr, hcost, hstate⟩ := hc first i q key rest hl F cap hi hq hm hb hcap hal hp
  exact ⟨hr, (SerdeKeyReuse.preciseCost_le_keyCost cfg F cap bs q key rest hlen hcap hm).trans hcost, hstate⟩

end WNear.Binary.SerdeStructObjKeyState
