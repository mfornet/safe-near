import Bridge.Methods.FtTotalSupply
import Bridge.Functions.FtTotalSupplyNone
import Bridge.Methods.FtTotalSupplyUninit

/-!
# `ft_total_supply` (296) on an uninitialized contract: the method panics

* `codeP_of`, `startResNone`: from the cells of the instantiated store, the resources
  `body296None` starts from: `startRes`'s, the panic path's code (`codeP`: 156, 521, 448, the
  trampoline 262 and the `panic_utf8` host, import 22) and its statics (`staticsResP`).
* `ft_adequate_none`: adequacy of `body296None` from the store after the entry activation: every
  run that ends, ends in a trap with the host after `storage_read` panicked with "The contract
  is not initialized", and at most `Cg` used.
* `ftTotalSupply_panics`: `MethodPanicsR cfg 296 preNone (costNone cfg) postNone`.
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupply WNear.Binary.InitialState
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicCode panicked notInit)

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- **The code of the panic path**, from the store's function cells. -/
theorem codeP_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ⊢
      codeP cfg.fees.numExtraBytesRecord 0 wInst id := by
  iintro ⟨#HF, #Hi⟩
  have h22 := PanicStr.wStore_panicUtf8 cfg h
  simp only [codeP, panicCode, id]
  repeat' (first
    | iexact Hi
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | (iapply funcLeaf cfg h 22 _ (by decide) h22; iexact HF)
    | isplitl [])

set_option maxRecDepth 100000 in
/-- **The resources of the start, with the panic path's**: `startRes_gen`'s, the panic path's
code and statics. -/
theorem startResNone_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code296 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
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
  ihave #Hk := code296_of cfg h $$ []
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
      |==> (code296 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗
        codeP cfg.fees.numExtraBytesRecord 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗ staticsP 0 0 id) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startResNone_gen wDataMem_image cfg h))

end Res

/-! ## Adequacy -/

/-- The cells `ft_total_supply` hands back on a trap, from the host `e` with no `STATE`: the
host after `storage_read` (`h1`) panicked with "The contract is not initialized", and the gas
counter within `Cg`. -/
def endCellsNone (Cg : Nat) (e : NearState) (st : Near.TrieOverlay.State)
    (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h1 h' : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    StorageReadPost e StateRead.stateKey 0 st h1 ∧
    erase h' = erase { h1 with lastError := some (.guestPanic notInitMsg) } ∧
    cs = [(Loc.host, .host (erase h')), (gasLoc, gasCellOf g p a)] ∧ g.used ≤ Cg

theorem endCellsNone_ends {Cg : Nat} {e : NearState} {st : Near.TrieOverlay.State} {σ' : MStore}
    {cs : List (Loc × Cell NearState)} (hc : endCellsNone Cg e st cs)
    (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h1, StorageReadPost e StateRead.stateKey 0 st h1 ∧
      erase σ'.store.host = erase { h1 with lastError := some (.guestPanic notInitMsg) } ∧
      σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h1, h', g, p, a, hq, he, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h1, hq, hh.trans he, hgg ▸ hg⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `ft_total_supply` on an uninitialized contract**, from the store after the
entry activation (host `h`, no `STATE`): every run that ends, ends in a trap, the host after
`storage_read` panicked with "The contract is not initialized", at most `Cg` used. -/
theorem ft_adequate_none (cfg : RuntimeConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (hr : ReadNone (erase h) st) (Cg : Nat)
    (hgas : h.gas.used + cost296None cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f296.body))
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
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0], 0, wInst⟩ 0 f296.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body296None cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0
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

/-! ## The method's run -/

/-- What `ft_total_supply` needs of the host on an uninitialized contract: no `STATE`, and the
premises of `storage_read` and `panic_utf8` (`ReadNone`). -/
def preNone (e : NearState) : Prop := ∃ st, ReadNone e st

/-- Its cost: the entry activation (9) and `cost296None`. -/
def costNone (cfg : RuntimeConfig) (e : NearState) : Nat :=
  9 * cfg.wasm.regularOpCost + cost296None cfg.wasm e

/-- What it does to the host: `storage_read`'s effect (`StorageReadPost`), then the panic with
"The contract is not initialized" as the last error. -/
def postNone (e e' : NearState) : Prop :=
  ∃ st h1, ReadNone e st ∧ StorageReadPost e StateRead.stateKey 0 st h1 ∧
    e' = erase { h1 with lastError := some (.guestPanic notInitMsg) }

/-- A run that ended in a trap, and did not exhaust its fuel, is that trap. -/
theorem trap_of_ending {cfg : WasmConfig} {r : Machine × Option FunctionCallError} {t : Trap} {σ : MStore}
    (herr : r.2 = none ∨ (∃ e, r.2 = some (.hostError e)) ∨ r.2 = some (.executionIssue .fuelExhausted))
    (hfuel : r.2 ≠ some (.executionIssue .fuelExhausted))
    (h : resultCode cfg r = (.finished (.trap t), σ)) : r = (.trap t σ.store, none) := by
  obtain ⟨m, err⟩ := r
  simp only at herr hfuel
  rcases herr with rfl | ⟨e, rfl⟩ | rfl
  · cases m with
    | next c => simp [resultCode] at h
    | done vs s => simp [resultCode] at h
    | trap r s =>
      simp only [resultCode, Prod.mk.injEq, MCode.finished.injEq, Ending.trap.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
  · simp [resultCode] at h
  · exact absurd rfl hfuel

/-- **`ft_total_supply` panics on an uninitialized contract** (`MethodPanicsR`). -/
theorem ftTotalSupply_panics (cfg : RuntimeConfig) :
    MethodPanicsR cfg 296 preNone (costNone cfg) postNone := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 296)) (entryCost cfg.wasm (.next (startW cfg h 296))) =
      (.next { startW cfg h 296 with store := wStore cfg (charged h (9 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_296, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costNone] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := ft_adequate_none cfg (charged h (9 * cfg.wasm.regularOpCost)) st hr Cg
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

end WNear.Binary.FtTotalSupplyMethod
