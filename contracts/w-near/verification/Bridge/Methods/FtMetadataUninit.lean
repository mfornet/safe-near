import Bridge.Methods.Statics309
import Bridge.Methods.Code306
import Bridge.Methods.StorageBalanceBoundsUninit

/-!
# `ft_metadata` (309) on an uninitialized contract

With no `STATE`, 309 panics exactly as `ft_total_supply` (296) and `storage_balance_bounds` (306)
do: `state_read` returns `None` and `unwrap_or_default` calls `Contract::default`, which panics
with "The contract is not initialized" (`FtMetadataBody.body309None`), before the metadata is
built. The premises and effect are 296's (`FtTotalSupplyMethod.preNone`, `postNone`), the cost
`costNone309`.

* `code309N_of`, `startResNone`: the code and the resources of the start (`staticsRes309P`, with
  1024 bytes of stack).
* `fm_adequate_none`: adequacy of `body309None`.
* `ftMetadata_panics`: `MethodPanicsR cfg 309 preNone (costNone309 cfg) postNone`.
* `ftMetadata_refines_uninit`: the clauses of `Refines` with no state; the model's step is the
  same panic, and its gas bound (`gas_309`: compute, the trie nodes and 138 bytes of return data)
  covers the path (`hbound_none309`).
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

section Leaves

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.FtMetadataBody
  WNear.Binary.StateRead WNear.Binary.StorageReadWrap WNear.Binary.ReadRegister
  WNear.Binary.Interface WNear.Binary.VecFromElem WNear.Binary.AllocZeroed WNear.Binary.BorshContract
  WNear.Binary.BorshFT WNear.Binary.BorshBytes WNear.Binary.BorshInt WNear.Binary.DropVec in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The code of `ft_metadata` on an absent `STATE`**, from the store's function cells. -/
theorem code309N_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048 ⊢
      code309N cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 := by
  iintro ⟨#HF, #Hi, #Hm⟩
  have h0 := wStore_readRegister cfg h
  obtain ⟨h1, h20, h43⟩ := wStore_hosts cfg h
  simp only [code309N, codeA, codeN309, stateCode, srCode, rrCode, ifaceCodeR,
    ifaceCode, vecCode, allocCode, sliceCode, contractCode, ftCode, bytesCode, rdCode, dropCode, VecWithCap.vecCode2, id]
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

namespace WNear.Binary.FtMetadataMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupply WNear.Binary.FtMetadataBody WNear.Binary.InitialState
  WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicCode panicked notInit)

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The resources of the start on an absent `STATE`, for `code309N`. -/
theorem startResNone_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code309N cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047552 1024 ∗
        statics309 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := tableOf $$ HT
  ihave HS := staticsRes309P hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  icases HS with ⟨Stk, HS, HSP⟩
  ihave #Hk := code309N_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  ihave #HP := codeP_of cfg h $$ []
  · iframe HF
    iunfold instPt; iexact Hi
  imodintro
  iframe Hk HP Hg Hh Hgas Stk HS
  isplitr
  · iunfold instPt
    iexact Hi
  iunfold staticsP
  iexact HSP

theorem startResNone (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (code309N cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047552 1024 ∗
        statics309 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startResNone_gen wDataMem_image cfg h))

end Res

/-! ## Adequacy and the run -/

theorem f309_frame : funcs[309 - 48]! = f309 := by kernel_rfl

theorem startW_thread (cfg : RuntimeConfig) (h : NearState) :
    (startW cfg h 309).thread = entryThread ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f309.body := by
  simp only [startW, wFrame, f309_frame, entryThread]
  rfl

theorem entryCost_309 (cfg : RuntimeConfig) (h : NearState) :
    entryCost cfg.wasm (.next (startW cfg h 309)) = 10 * cfg.wasm.regularOpCost := by
  have ht := startW_thread cfg h
  simp only [entryCost, Config.locals, ht, entryThread, activationGas]
  simp [ValType.default]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `ft_metadata` on an uninitialized contract**: every run that ends, ends in a
trap, the host after `storage_read` panicked with "The contract is not initialized", at most
`Cg` used. -/
theorem fm_adequate_none (cfg : RuntimeConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone (erase h) st) (Cg : Nat)
    (hgas : h.gas.used + cost309None cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f309.body))
      ⟨wStore cfg h⟩
      (fun v σ' => (∃ r, v = .trap r) ∧ ∃ cs, endCellsNone Cg (erase h) st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => ∃ r, v = .trap r)
    (fun _ cs => endCellsNone Cg (erase h) st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜∃ r, v = .trap r⌝ ∗ mcellsSat (fun cs => endCellsNone Cg (erase h) st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (startResNone cfg h).trans ?_
  iintro H
  iapply fupd_wp
  imod H with ⟨#Hk, #HP, #Hi, Hg, Hh, Hgas, Stk, HS, HSP⟩
  imodintro
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f309.body Cg Ψ
  isplitr
  · iexact Hi
  icases BorshFT.stkSp 240 784 rfl $$ Stk with ⟨-, Stk⟩
  ihave Stk := BorshFT.stkA (a := 1047552 + 240) (b := (1048576 : UInt32).toNat - 784) rfl $$ Stk
  iunfold statics309 at HS
  icases HS with ⟨HS, -⟩
  rw [← mhostPt_erase h]
  iapply body309None cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0
    Interface.wInst_ifaceMod (by decide) Cg 0 { type := .num .i32, mutable := true } 1048576 (by decide)
    (by decide) 0 0 123 1051836 2048 memLen (erase h) st hr (entryPost Cg 0 Ψ)
  iframe Hk HP Stk HS HSP
  isplitl [Hgas]
  · iunfold credits
    iexists h.gas, h.gasProfile, h.actionProfile
    iframe Hgas
    ipureintro
    simp only [Near.GasCounter.used] at hgas ⊢
    omega
  isplitl [Hg]
  · iapply g0_pt $$ Hg
  isplitl [Hh]
  · iexact Hh
  iintro %h1 %hq HT
  simp only [entryPost]
  iintro %r
  iunfold panicked at HT
  icases HT with ⟨%h', %he, Hh, %R, Hc⟩
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, %a, Hg', %hg⟩
  isplitr
  · ipureintro; exact ⟨r, rfl⟩
  iexists [(Loc.host, Cell.host (erase h')), (gasLoc, gasCellOf g p a)]
  isplitr
  · ipureintro
    refine ⟨⟨h1, h', g, p, a, hq, ?_, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
    rw [he, PanicStr.notInit_utf8String]
    rfl
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hh]
  · iunfold mhostPt at Hh
    iexact Hh
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hg']
  · iunfold gasPt at Hg'
    iexact Hg'
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- The cost of the panic path: the entry activation (10) and `cost309None`. -/
def costNone309 (cfg : RuntimeConfig) (e : NearState) : Nat :=
  10 * cfg.wasm.regularOpCost + cost309None cfg.wasm e

/-- **`ft_metadata` panics on an uninitialized contract** (`MethodPanicsR`). -/
theorem ftMetadata_panics (cfg : RuntimeConfig) :
    MethodPanicsR cfg 309 preNone (costNone309 cfg) postNone := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 309)) (entryCost cfg.wasm (.next (startW cfg h 309))) =
      (.next { startW cfg h 309 with store := wStore cfg (charged h (10 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_309, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costNone309] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := fm_adequate_none cfg (charged h (10 * cfg.wasm.regularOpCost)) st hr Cg
    (by rw [charged_gas_used, erase_charged]; simp only [costNone309] at hcost; omega)
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
  rw [← startW_thread cfg h] at had
  have hend := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hend
  obtain ⟨⟨t, rfl⟩, cs, hcs, hlk⟩ := hend
  have hrun := trap_of_ending (runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h1, hq, he, hu⟩ := endCellsNone_ends hcs hlk
  exact ⟨t, σ.store, hrun, ⟨st, h1, hr, hq, he⟩, hu⟩

/-! ## The clauses of `Refines` -/

open NearInterface

set_option maxRecDepth 100000 in
theorem funcType_309 : wNearModule.funcType? 309 = some { params := [], results := [] } := by kernel_rfl

theorem export_309 : wNearModule.exportFunc? "ft_metadata" = some 309 := by decide

theorem step_none (cfg : WNear.Config) (ctx : Context) :
    (WNear.wnear cfg).step ctx none .ftMetadata =
      .error { failure := .panic .notInitialized, logs := [] } := by
  rfl

/-- The model's step on no state agrees with the panic, from a host with no logs. -/
theorem agreesPanic_none' (cfg : WNear.Config) (ctx : Context) (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) notInitMsg e ((WNear.wnear cfg).step ctx none .ftMetadata) :=
  ⟨_, step_none cfg ctx, rfl, hl.symm⟩

/-- The model's gas bound for `ft_metadata`: compute, the trie nodes and the data receipts of
the 138 bytes of the metadata's JSON. -/
theorem gas_309 (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) :
    (WNear.wnear cfg).gas ctx st .ftMetadata =
      WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 138 := by
  show WNear.gasBound ctx .ftMetadata = _
  simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
    WNear.Call.resultBytes, returnBytes_ftMetadata]
  simp

open FtTotalSupply in
/-- **The model's gas bound covers loading and the panic path.** -/
theorem hbound_none309 (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (size : Nat) (hval : (hostOf ctx raw).storage WNear.stateKey = none) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + costNone309 ctx.protocol (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .ftMetadata := by
  have htrie := trie_le ctx raw
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hv : (erase (hostOf ctx raw)).storage StateRead.stateKey = none := by
    rw [StateRead.stateKey_eq]; exact hval
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  rw [gas_309, hl]
  have hrn := readNodes_of_false (h := erase (hostOf ctx raw)) rfl
  simp only [costNone309, cost309None, costBNone, storageReadUse, storageReadPhaseUse, hv, hrn, Nat.zero_mul, Nat.zero_add, Option.map_none,
    Option.getD_none, panicUtf8Use, panicUtf8Charges, storageReadBeforeCharges, chargesUse, chargeUse,
    List.map, List.sum_cons, List.sum_nil, hx'] at htrie ⊢
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.base; have := hc.loadingBase; have := hc.readMemoryBase
  have := hc.readMemoryByte; have := hc.storageReadBase; have := hc.storageReadKeyByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  omega

open ContractModel in
/-- **`ft_metadata` refines the model on an uninitialized contract**: with no state, the binary
panics with "The contract is not initialized", as the model's step does. Left: the code size,
`CostsV86` and `LimitsV86`. -/
theorem ftMetadata_refines_uninit (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none) (hm : ctx.method = "ft_metadata")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none .ftMetadata
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none .ftMetadata ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none .ftMetadata) →
      Matches (WNear.wnear cfg) ctx raw r res ∧
        r.usedGas ≤ (WNear.wnear cfg).gas ctx none .ftMetadata) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  subst hraw
  have hval : (hostOf ctx ∅).storage WNear.stateKey = none := hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := preNone_of_ctx cfg ctx ∅ none hwf hl hc hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf ∅ none ctx .ftMetadata preNone
    (costNone309 ctx.protocol) postNone notInitMsg hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_309)
    funcType_309 (by decide) (by decide) (ftMetadata_panics ctx.protocol) hpre hpreP
    (fun e he => postNone_panicHost rfl he) (fun e he => postNone_panicHost rfl he)
    (fun e he => agreesPanic_none' cfg ctx e (postNone_logs rfl he))
    (fun e he => agreesPanic_none' cfg ctx e (postNone_logs rfl he))
    (hbound_none309 cfg ctx ∅ none size hval hc hsize)

end WNear.Binary.FtMetadataMethod
