import Bridge.Methods.Code296
import Bridge.Methods.Statics309
import Bridge.Functions.FtMetadataInit

/-!
# The code `ft_metadata` runs on an initialized contract, from the instantiated store

`code309_of`: as `code306_of`, the persistent function cells of `wStore`, the instance and the
memory limit give `FtMetadataBody.code309` for `wInst`: the getter (308), the struct serializer
(102) and its fields, the grow path of `write_all` (`VecGrow`: 716, 714, 312, 238, 154 and the
allocator) and the drops.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.FtMetadataBody
  WNear.Binary.StateRead WNear.Binary.StorageReadWrap WNear.Binary.ReadRegister
  WNear.Binary.Interface WNear.Binary.VecFromElem WNear.Binary.AllocZeroed WNear.Binary.BorshContract
  WNear.Binary.BorshFT WNear.Binary.BorshBytes WNear.Binary.BorshInt WNear.Binary.DropVec
  WNear.Binary.SerializeStr WNear.Binary.VecAppend WNear.Binary.VecWithCap WNear.Binary.MetadataGetter
  WNear.Binary.MetadataFields WNear.Binary.MetadataStruct WNear.Binary.VecGrow WNear.Binary.AllocTwo in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **The code of `ft_metadata`**, from the store's function cells. -/
theorem code309_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      code309 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := wStore_hosts cfg h
  simp only [code309, codeA, codeM309, codeC309, codeC, stateCode, srCode, rrCode, ifaceCodeR,
    ifaceCode, vecCode, allocCode, sliceCode, contractCode, ftCode, bytesCode, rdCode, dropCode,
    strCode, vecCode2, metaCode, mfCode, serCode, escCode, appCode, waCode, growCode, reallocCode,
    code310, id]
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
