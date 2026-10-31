import Bridge.Methods.Statics297Object
import Bridge.Functions.FromSliceSpec

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/

namespace WNear.Binary.InitialState
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open WNear.Binary.Interface (dataWord dataWord_eq)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BalanceOf297AbsentCall
open WNear.Binary.FtTotalSupply (statics)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000

theorem startRes297Provider_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (FromSliceSpec.codeCtx cfg h ∗ code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ SerdeIgnValue.code81 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ frame297 0 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗
        (PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := table297Of $$ HT
  ihave HS := statics297PObj hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  ihave #Hk := code297_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  ihave #HIgn := ignored_code_of cfg h $$ [HF]
  · iframe HF
    iunfold instPt
    iexact Hi
  imodintro
  isplitr
  · iunfold FromSliceSpec.codeCtx
    iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  iframe HIgn Hk Hg Hh Hgas HS
  iunfold instPt
  iexact Hi

theorem startRes297Provider (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (FromSliceSpec.codeCtx cfg h ∗ code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ SerdeIgnValue.code81 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ frame297 0 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗
        (PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startRes297Provider_gen wDataMem_image cfg h))

end WNear.Binary.InitialState
