import Bridge.Methods.Code296
import Bridge.Methods.Statics306

/-!
# The code `storage_balance_bounds` runs, from the instantiated store

`code306_of`: as `code231_of`, the persistent function cells of `wStore`, the instance and the
memory limit give `StorageBalanceBoundsBody.code306` for `wInst`.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.StorageBalanceBoundsBody
  WNear.Binary.StateRead WNear.Binary.StorageReadWrap WNear.Binary.ReadRegister
  WNear.Binary.Interface WNear.Binary.VecFromElem WNear.Binary.AllocZeroed WNear.Binary.BorshContract
  WNear.Binary.BorshFT WNear.Binary.BorshBytes WNear.Binary.BorshInt WNear.Binary.DropVec WNear.Binary.ToVec
  WNear.Binary.ToString WNear.Binary.FmtDisplay WNear.Binary.FmtSink WNear.Binary.SerializeStr
  WNear.Binary.VecAppend WNear.Binary.VecWithCap WNear.Binary.SerdeStruct in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The code of `storage_balance_bounds`**, from the store's function cells. -/
theorem code306_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      code306 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := wStore_hosts cfg h
  simp only [code306, codeA, codeM306, codeC, stateCode, srCode, rrCode, ifaceCodeR,
    ifaceCode, vecCode, allocCode, sliceCode, contractCode, ftCode, bytesCode, rdCode, dropCode,
    structCode, fieldCode, tsCode, fmtCode, sinkCode, serCode, escCode, appCode, vecCode2, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | isplitl [])

end Leaves

end WNear.Binary.InitialState
