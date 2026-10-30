import Bridge.Methods.CodeNew
import Bridge.Functions.NewBodyOk

/-!
# The code `new` (290) runs on its success path, from the instantiated store

`codeNewS_of`: as `codeNewP_of`, the persistent function cells of `wStore`, the instance and the
memory limit give `NewBody.codeNewS` for `wInst`: `Contract::new` (289) and `state_write` (220)
with everything they call, among them the hosts `storage_usage` (10), `storage_write` (42),
`storage_remove` (44), `read_register` (0) and `register_len` (1).
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.NewBody WNear.Binary.Interface WNear.Binary.ContractNew WNear.Binary.MeasureUsage
  WNear.Binary.LookupMapOps WNear.Binary.LookupMapInsert WNear.Binary.LookupMapRemove WNear.Binary.LookupMapBorsh
  WNear.Binary.LookupMapLeaves WNear.Binary.LookupMapLeavesF WNear.Binary.VecWithCap
  WNear.Binary.AllocZeroed WNear.Binary.EnvGetters WNear.Binary.StorageWrite WNear.Binary.StorageRemove
  WNear.Binary.ReadRegister WNear.Binary.ReadRegisterF WNear.Binary.DropVec WNear.Binary.StateWrite
  WNear.Binary.BorshSer WNear.Binary.BorshFT WNear.Binary.BorshBytes WNear.Binary.BorshInt
  WNear.Binary.BorshContract WNear.Binary.VecFromElem WNear.Binary.VecFromElemF WNear.Binary.AllocZeroedF
  WNear.Binary.AllocTwoWalk WNear.Binary.AllocTwo in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The code of `new`'s success path**, from the store's function cells. -/
theorem codeNewS_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      codeNewS cfg.fees.numExtraBytesRecord 0 2048 0 wInst id (some 2048) := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := wStore_hosts cfg h
  have h10 := (wStore_envGetters cfg h).1
  have h42 := wStore_storageWrite cfg h
  have h44 := wStore_storageRemove cfg h
  simp only [codeNewS, code289, code107, code404, code401, code402, code391, code393, code395, code397, code377,
    code376, code398, code510, code519, code392, rr550Code, rr550CodeF, vecCode2, allocCode, uCode, wCode, rCode,
    ifaceCodeR, rrCode, rrCodeF, ifaceCode, dropCode, swCode, ser163Code, ser164Code, ftSerCode, BorshSer.serCode,
    ftCode, bytesCode, rdCode, contractCode, sliceCode, vecCode, vecCodeF, code575F, code7, code575, code310, VecAppend.appCode, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 0 _ (by decide) h0; iexact HF)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | (iapply funcLeaf cfg h 10 _ (by decide) h10; iexact HF)
    | (iapply funcLeaf cfg h 42 _ (by decide) h42; iexact HF)
    | (iapply funcLeaf cfg h 44 _ (by decide) h44; iexact HF)
    | isplitl [])

end Leaves

end WNear.Binary.InitialState
