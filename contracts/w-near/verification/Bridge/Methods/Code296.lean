import Bridge.Methods.StartCells

/-!
# The code `ft_total_supply` runs, from the instantiated store

`code296_of`: the persistent function cells of `wStore` (`funcCells`, made persistent by
`persistList`), the instance and the memory limit give `FtTotalSupply.code296` for `wInst`
(function `k` at address `k`, `A = id`). Each defined function `k` is `funcs[k - 48]!`
(`wasmLeaf`, the identity checked by the kernel), each host import as `wStore` links it.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

theorem wStore_func (cfg : RuntimeConfig) (h : NearState) (k : Nat) (h1 : 48 ≤ k) (h2 : k < 955) :
    (wStore cfg h).funcs[k]? = some (.wasm types[funcs[k - 48]!.type]! 0 funcs[k - 48]!) := by
  have hi : k - 48 < funcs.size := by rw [funcs_size]; omega
  simp only [wStore]
  rw [Array.getElem?_append_right (by simp [wHosts_length]; omega)]
  simp only [List.size_toArray, List.length_map, wHosts_length, List.getElem?_toArray, List.getElem?_map,
    Array.getElem?_toList, Array.getElem?_eq_getElem hi, Option.map_some, getElem!_pos funcs (k - 48) hi]

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem funcLeaf (cfg : RuntimeConfig) (h : NearState) (k : Nat) (f : FuncInst NearState) (hk : k < 955)
    (hf : (wStore cfg h).funcs[k]? = some f) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ⊢ (k ↪[wf] f : IProp GF) := by
  have hl : (funcCells cfg h)[k]? = some (Loc.func k, .func f) := by
    rw [funcCells, List.getElem?_map, List.getElem?_range hk, Option.map_some, Array.getD_eq_getD_getElem?, hf]
    rfl
  generalize funcCells cfg h = l at hl ⊢
  have e := BigSepL.bigSepL_lookup (PROP := IProp GF) (Φ := fun _ (p : Loc × Cell NearState) => iprop(p.1 ↦ₛ□ p.2)) hl
  exact e

theorem wasmLeaf (cfg : RuntimeConfig) (h : NearState) (k : Nat) (fk : Func) (t : Nat) (h1 : 48 ≤ k)
    (h2 : k < 955) (hf : funcs[k - 48]! = fk) (ht : fk.type = t) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ⊢ (k ↪[wf] FuncInst.wasm types[t]! 0 fk : IProp GF) := by
  subst hf ht
  exact funcLeaf cfg h k _ h2 (wStore_func cfg h k h1 h2)

open WNear.Binary.FtTotalSupply WNear.Binary.StateRead WNear.Binary.StorageReadWrap WNear.Binary.ReadRegister
  WNear.Binary.Interface WNear.Binary.VecFromElem WNear.Binary.AllocZeroed WNear.Binary.BorshContract
  WNear.Binary.BorshFT WNear.Binary.BorshBytes WNear.Binary.BorshInt WNear.Binary.DropVec WNear.Binary.ToVec
  WNear.Binary.ToString WNear.Binary.FmtDisplay WNear.Binary.FmtSink WNear.Binary.SerializeStr
  WNear.Binary.VecAppend WNear.Binary.VecWithCap in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The code of `ft_total_supply`**, from the store's function cells. -/
theorem code296_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      code296 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := wStore_hosts cfg h
  simp only [code296, codeA, codeB, codeC, stateCode, srCode, rrCode, ifaceCodeR, ifaceCode, vecCode,
    allocCode, sliceCode, contractCode, ftCode, bytesCode, rdCode, dropCode, tvCode, tsCode, fmtCode, sinkCode,
    serCode, escCode, appCode, vecCode2, id]
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
