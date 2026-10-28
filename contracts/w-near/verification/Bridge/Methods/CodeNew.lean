import Bridge.Methods.Code296
import Bridge.Functions.NewBodyPanic

/-!
# The code `new` (290) runs on its panic paths, from the instantiated store

`codeNewP_of`: as `code306_of`, the persistent function cells of `wStore`, the instance and the
memory limit give `NewBody.codeNewP` for `wInst`: the prologue's code, `attached_deposit` (529,
444, the trampoline 253 and the host 13), `state_exists` (552, 551, 436, the trampoline 286 and
the host 45) and `panic_str` (521, 448, the trampoline 262 and the host 22).
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.FtTotalSupply WNear.Binary.NewBody WNear.Binary.Interface WNear.Binary.PanicStr
  WNear.Binary.EnvGetters WNear.Binary.StorageHasKey in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The code of `new`'s panic paths**, from the store's function cells. -/
theorem codeNewP_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      codeNewP cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) := by
  iintro ⟨#HF, #Hi, #Hm⟩
  obtain ⟨h1, h20, h43⟩ := wStore_hosts cfg h
  have h13 := (wStore_envGetters cfg h).2
  have h45 := wStore_storageHasKey cfg h
  have h22 := wStore_panicUtf8 cfg h
  simp only [codeNewP, codeA, ifaceCode, dCode, hCode, panicCode, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 1 _ (by decide) h1; iexact HF)
    | (iapply funcLeaf cfg h 20 _ (by decide) h20; iexact HF)
    | (iapply funcLeaf cfg h 43 _ (by decide) h43; iexact HF)
    | (iapply funcLeaf cfg h 13 _ (by decide) h13; iexact HF)
    | (iapply funcLeaf cfg h 45 _ (by decide) h45; iexact HF)
    | (iapply funcLeaf cfg h 22 _ (by decide) h22; iexact HF)
    | isplitl [])

end Leaves

end WNear.Binary.InitialState
