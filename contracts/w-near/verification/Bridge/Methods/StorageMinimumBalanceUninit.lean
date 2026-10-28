import Bridge.Methods.StorageMinimumBalance
import Bridge.Methods.FtTotalSupplyUninitRefines

/-!
# `storage_minimum_balance` (231) on an uninitialized contract

With no `STATE`, 231 panics exactly as `ft_total_supply` (296) does: `state_read` returns
`None` and `unwrap_or_default` calls `Contract::default`, which panics with "The contract is not
initialized" (`body231None`, through the shared prefix `U128View.bodyViewNone`). The premises,
cost and effect are 296's (`FtTotalSupplyMethod.preNone`, `costNone`, `postNone`).

* `smb_adequate_none`: adequacy of `body231None`.
* `storageMinimumBalance_panics`: `MethodPanicsR cfg 231 preNone (costNone cfg) postNone`.
* `storageMinimumBalance_refines_uninit`: the clauses of `Refines` with no state; the model's
  step is the same panic (`agreesPanic_none'`), and the gas bound of the call is
  `ft_total_supply`'s (`gas_eq`).
-/

namespace WNear.Binary.StorageMinimumBalanceMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupply WNear.Binary.StorageMinimumBalance WNear.Binary.InitialState
  WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicCode panicked notInit)

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The resources of the start with the panic path's, for `code231`. -/
theorem startResNone_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code231 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := tableOf $$ HT
  ihave HS := staticsResP hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  icases HS with ⟨Stk, HS, HSP⟩
  ihave #Hk := code231_of cfg h $$ []
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
      |==> (code231 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startResNone_gen wDataMem_image cfg h))

end Res

/-! ## Adequacy and the run -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `storage_minimum_balance` on an uninitialized contract**: every run that ends,
ends in a trap, the host after `storage_read` panicked with "The contract is not initialized",
at most `Cg` used. -/
theorem smb_adequate_none (cfg : RuntimeConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone (erase h) st) (Cg : Nat)
    (hgas : h.gas.used + cost296None cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f231.body))
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
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0], 0, wInst⟩ 0 f231.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body231None cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0
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

/-- **`storage_minimum_balance` panics on an uninitialized contract** (`MethodPanicsR`). -/
theorem storageMinimumBalance_panics (cfg : RuntimeConfig) :
    MethodPanicsR cfg 231 preNone (costNone cfg) postNone := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 231)) (entryCost cfg.wasm (.next (startW cfg h 231))) =
      (.next { startW cfg h 231 with store := wStore cfg (charged h (9 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_231, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costNone] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := smb_adequate_none cfg (charged h (9 * cfg.wasm.regularOpCost)) st hr Cg
    (by rw [charged_gas_used, erase_charged]; simp only [costNone] at hcost; omega)
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
    (WNear.wnear cfg).step ctx none .storageMinimumBalance =
      .error { failure := .panic .notInitialized, logs := [] } := by
  rfl

/-- The model's step on no state agrees with the panic, from a host with no logs. -/
theorem agreesPanic_none' (cfg : WNear.Config) (ctx : Context) (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) notInitMsg e ((WNear.wnear cfg).step ctx none .storageMinimumBalance) :=
  ⟨_, step_none cfg ctx, rfl, hl.symm⟩

/-- The model's gas bound for `storage_minimum_balance` is `ft_total_supply`'s: both are views
with no arguments returning a `u128`. -/
theorem gas_eq (cfg : WNear.Config) (ctx : Context) (st : Option WNear.State) :
    (WNear.wnear cfg).gas ctx st .storageMinimumBalance = (WNear.wnear cfg).gas ctx st .ftTotalSupply := rfl

open ContractModel in
/-- **`storage_minimum_balance` refines the model on an uninitialized contract**: with no state,
the binary panics with "The contract is not initialized", as the model's step does. -/
theorem storageMinimumBalance_refines_uninit (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw none) (hm : ctx.method = "storage_minimum_balance")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol) (hsize : size ≤ 185625) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx none .storageMinimumBalance
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx none .storageMinimumBalance ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx none .storageMinimumBalance) →
      Matches (WNear.wnear cfg) ctx raw r res ∧
        r.usedGas ≤ (WNear.wnear cfg).gas ctx none .storageMinimumBalance) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hraw : raw = ∅ := hrep
  subst hraw
  have hval : (hostOf ctx ∅).storage WNear.stateKey = none := hostOf_storage_empty ctx _
  obtain ⟨hpre, hpreP⟩ := preNone_of_ctx cfg ctx ∅ none hwf hl hc hval
  exact method_refines_callP (WNear.wnear cfg) size codeOf ∅ none ctx .storageMinimumBalance preNone
    (costNone ctx.protocol) postNone notInitMsg hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_231)
    funcType_231 (by decide) (by decide) (storageMinimumBalance_panics ctx.protocol) hpre hpreP
    (fun e he => postNone_panicHost rfl he) (fun e he => postNone_panicHost rfl he)
    (fun e he => agreesPanic_none' cfg ctx e (postNone_logs rfl he))
    (fun e he => agreesPanic_none' cfg ctx e (postNone_logs rfl he))
    (hbound_none cfg ctx ∅ none size hval hc hsize)

end WNear.Binary.StorageMinimumBalanceMethod
