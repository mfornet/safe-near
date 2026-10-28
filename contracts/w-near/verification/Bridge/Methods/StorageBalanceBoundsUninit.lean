import Bridge.Methods.StorageBalanceBounds
import Bridge.Methods.FtTotalSupplyUninitRefines

/-!
# `storage_balance_bounds` (306) on an uninitialized contract

With no `STATE`, 306 panics exactly as `ft_total_supply` (296) does: `state_read` returns
`None` and `unwrap_or_default` calls `Contract::default`, which panics with "The contract is not
initialized" (`body306None`). The premises and effect are 296's (`FtTotalSupplyMethod.preNone`, `postNone`), the cost `costNone306`.

* `sbb_adequate_none`: adequacy of `body306None`.
* `storageBalanceBounds_panics`: `MethodPanicsR cfg 306 preNone (costNone306 cfg) postNone`.
* `storageBalanceBounds_refines_uninit`: the clauses of `Refines` with no state; the model's
  step is the same panic (`agreesPanic_none'`), and the gas bound covers the path
  (`hbound_none306`; the model's bound `gas_306`, 97 bytes of return data, `retBytes306`).
-/

namespace WNear.Binary.StorageBalanceBoundsMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupply WNear.Binary.StorageBalanceBoundsBody WNear.Binary.InitialState
  WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicCode panicked notInit)

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The resources of the start with the panic path's, for `code306`. -/
theorem startResNone_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code306 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        StorageBalanceBoundsBody.statics306 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := tableOf $$ HT
  ihave HS := staticsRes306P hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  icases HS with ⟨Stk, HS, HSP⟩
  ihave #Hk := code306_of cfg h $$ []
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
      |==> (code306 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        StorageBalanceBoundsBody.statics306 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startResNone_gen wDataMem_image cfg h))

end Res

/-! ## Adequacy and the run -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `storage_balance_bounds` on an uninitialized contract**: every run that ends,
ends in a trap, the host after `storage_read` panicked with "The contract is not initialized",
at most `Cg` used. -/
theorem sbb_adequate_none (cfg : RuntimeConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone (erase h) st) (Cg : Nat)
    (hgas : h.gas.used + cost306None cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f306.body))
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
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f306.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body306None cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0
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

/-- The cost of the panic path: the entry activation (10) and `cost306None`. -/
def costNone306 (cfg : RuntimeConfig) (e : NearState) : Nat :=
  10 * cfg.wasm.regularOpCost + cost306None cfg.wasm e

/-- **`storage_balance_bounds` panics on an uninitialized contract** (`MethodPanicsR`). -/
theorem storageBalanceBounds_panics (cfg : RuntimeConfig) :
    MethodPanicsR cfg 306 preNone (costNone306 cfg) postNone := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 306)) (entryCost cfg.wasm (.next (startW cfg h 306))) =
      (.next { startW cfg h 306 with store := wStore cfg (charged h (10 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_306, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costNone306] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := sbb_adequate_none cfg (charged h (10 * cfg.wasm.regularOpCost)) st hr Cg
    (by rw [charged_gas_used, erase_charged]; simp only [costNone306] at hcost; omega)
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

theorem step_none (cfg : WNear.Config) (ctx : Context) :
    (WNear.wnear cfg).step ctx none .storageBalanceBounds =
      .error { failure := .panic .notInitialized, logs := [] } := by
  rfl

/-- The model's step on no state agrees with the panic, from a host with no logs. -/
theorem agreesPanic_none' (cfg : WNear.Config) (ctx : Context) (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) notInitMsg e ((WNear.wnear cfg).step ctx none .storageBalanceBounds) :=
  ⟨_, step_none cfg ctx, rfl, hl.symm⟩

/-- The longest JSON `storage_balance_bounds` returns: both bounds `2^128 - 1`, 97 bytes. -/
theorem retBytes306 :
    (WNear.Ret.storageBalanceBounds { min := WNear.u128Bound - 1, max := some (WNear.u128Bound - 1) }).json.utf8ByteSize
      = 97 := by
  decide

/-- The model's gas bound for `storage_balance_bounds`: compute, the trie nodes and the data
receipts of 97 bytes. -/
theorem gas_306 (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) :
    (WNear.wnear cfg).gas ctx st .storageBalanceBounds =
      WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 97 := by
  show WNear.gasBound ctx .storageBalanceBounds = _
  simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
    WNear.Call.resultBytes, WNear.Call.returnBytes, retBytes306]
  simp

open FtTotalSupply in
/-- **The model's gas bound covers loading and the panic path.** -/
theorem hbound_none306 (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (size : Nat) (hval : (hostOf ctx raw).storage WNear.stateKey = none) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + costNone306 ctx.protocol (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .storageBalanceBounds := by
  have htrie := trie_le ctx raw
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hv : (erase (hostOf ctx raw)).storage StateRead.stateKey = none := by
    rw [StateRead.stateKey_eq]; exact hval
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  rw [gas_306, hl]
  have hrn := readNodes_of_false (h := erase (hostOf ctx raw)) rfl
  simp only [costNone306, cost306None, costBNone, storageReadUse, storageReadPhaseUse, hv, hrn, Nat.zero_mul, Nat.zero_add, Option.map_none,
    Option.getD_none, panicUtf8Use, panicUtf8Charges, storageReadBeforeCharges, chargesUse, chargeUse,
    List.map, List.sum_cons, List.sum_nil, hx'] at htrie ⊢
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.base; have := hc.loadingBase; have := hc.readMemoryBase
  have := hc.readMemoryByte; have := hc.storageReadBase; have := hc.storageReadKeyByte
  have := hc.utf8DecodingBase; have := hc.utf8DecodingByte
  omega

open ContractModel in
/-- **`storage_balance_bounds` refines the model on an uninitialized contract**: with no state,
the binary panics with "The contract is not initialized", as the model's step does. -/
theorem storageBalanceBounds_refines_uninit (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none) (hm : ctx.method = "storage_balance_bounds")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none .storageBalanceBounds
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none .storageBalanceBounds ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none .storageBalanceBounds) →
      Matches (WNear.wnear cfg) ctx raw r res ∧
        r.usedGas ≤ (WNear.wnear cfg).gas ctx none .storageBalanceBounds) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  subst hraw
  have hval : (hostOf ctx ∅).storage WNear.stateKey = none := hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := preNone_of_ctx cfg ctx ∅ none hwf hl hc hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf ∅ none ctx .storageBalanceBounds preNone
    (costNone306 ctx.protocol) postNone notInitMsg hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_306)
    funcType_306 (by decide) (by decide) (storageBalanceBounds_panics ctx.protocol) hpre hpreP
    (fun e he => postNone_panicHost rfl he) (fun e he => postNone_panicHost rfl he)
    (fun e he => agreesPanic_none' cfg ctx e (postNone_logs rfl he))
    (fun e he => agreesPanic_none' cfg ctx e (postNone_logs rfl he))
    (hbound_none306 cfg ctx ∅ none size hval hc hsize)

end WNear.Binary.StorageBalanceBoundsMethod
