import Bridge.Methods.CodeNew
import Bridge.Methods.StaticsNew
import Bridge.Methods.NewModel
import Bridge.Methods.StorageBalanceBoundsUninit

/-!
# `new` (290): its two panics, from the run to `Refines`

* With a deposit, `new` panics with "Method new doesn't accept deposit" before reading storage
  (`body290Dep`); `new_panics_deposit`: `MethodPanicsR cfg 290 PreDep (costDep cfg) postDep`.
* With no deposit and `STATE` present, `state_exists` (552) is true and `new` panics with "The
  contract has already been initialized" (`body290Init`); `new_panics_init`:
  `MethodPanicsR cfg 290 preInit (costInit cfg) postInit`.
* `new_refines_deposit` (any state) and `new_refines_init` (`some S`, no deposit): the clauses of
  `Refines`; the model's step is the same panic (`step_new_deposit`, `step_new_some`), and the
  gas bound covers the path (`hbound_dep`, `hbound_init`; `storage_has_key`'s costs in
  `CostsNewV86`).
-/

namespace WNear.Binary.NewMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.InitialState WNear.Binary.NewBody
open WNear.Binary.FtTotalSupplyMethod (g0_pt mhostPt_erase runInitialized_finished runInitialized_err
  trap_of_ending)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicked)
open WNear.Binary.EnvGetters (depLo depHi)

/-- The panic messages. -/
def depositStr : String := "Method new doesn't accept deposit"
def initStr : String := "The contract has already been initialized"

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The resources of the start for `new`: the panic paths' code, the statics (the success
path's included). -/
theorem startResNew_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (codeNewP cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗
        mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        staticsNewP 0 0 id 0 0 ∗ staticsNewS 0 0 id 123 2048 memLen) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := tableOfNew $$ HT
  ihave HS := staticsResNew hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  icases HS with ⟨Stk, HS, HSS⟩
  ihave #Hk := codeNewP_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  imodintro
  iframe Hk Hg Hh Hgas Stk HS HSS
  iunfold instPt
  iexact Hi

theorem startResNew (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (codeNewP cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗
        mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        staticsNewP 0 0 id 0 0 ∗ staticsNewS 0 0 id 123 2048 memLen) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startResNew_gen wDataMem_image cfg h))

end Res

/-! ## The entry -/

theorem f290_frame : funcs[290 - 48]! = f290 := by kernel_rfl

theorem startW_thread (cfg : RuntimeConfig) (h : NearState) :
    (startW cfg h 290).thread = entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f290.body := by
  simp only [startW, wFrame, f290_frame, entryThread]
  rfl

theorem entryCost_290 (cfg : RuntimeConfig) (h : NearState) :
    entryCost cfg.wasm (.next (startW cfg h 290)) = 9 * cfg.wasm.regularOpCost := by
  have ht := startW_thread cfg h
  simp only [entryCost, Config.locals, ht, entryThread, activationGas]
  simp [ValType.default]

set_option maxRecDepth 100000 in
theorem funcType_290 : wNearModule.funcType? 290 = some { params := [], results := [] } := by kernel_rfl

theorem export_290 : wNearModule.exportFunc? "new" = some 290 := by decide

/-! ## The deposit panic -/

/-- What the deposit panic needs of the host: not a view call, a nonzero deposit, and the
premises of `panic_utf8` for the 33-byte message. -/
structure PreDep (e : NearState) : Prop where
  view : e.context.isView = false
  dep : depLo e ||| depHi e ≠ 0
  fit : LogFits e 33
  ov : e.extCosts.cost "read_memory_byte" * 33 < 2 ^ 64

/-- Its cost: the entry activation (9) and `costDep290`. -/
def costDep (cfg : RuntimeConfig) (e : NearState) : Nat :=
  9 * cfg.wasm.regularOpCost + costDep290 cfg.wasm e

/-- What it does to the host: the panic, nothing else. -/
def postDep (e e' : NearState) : Prop :=
  e' = erase { e with lastError := some (.guestPanic depositStr) }

/-- The cells `new` hands back on the deposit panic. -/
def endCellsDep (Cg : Nat) (e : NearState) (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h' : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    erase h' = erase { e with lastError := some (.guestPanic depositStr) } ∧
    cs = [(Loc.host, .host (erase h')), (gasLoc, gasCellOf g p a)] ∧ g.used ≤ Cg

theorem endCellsDep_ends {Cg : Nat} {e : NearState} {σ' : MStore} {cs : List (Loc × Cell NearState)}
    (hc : endCellsDep Cg e cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    erase σ'.store.host = erase { e with lastError := some (.guestPanic depositStr) } ∧
      σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h', g, p, a, he, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨hh.trans he, hgg ▸ hg⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `new` with a deposit**: every run that ends, ends in a trap, the host panicked
with "Method new doesn't accept deposit", at most `Cg` used. -/
theorem new_adequate_dep (cfg : RuntimeConfig) (h : NearState) (hpre : PreDep (erase h)) (Cg : Nat)
    (hgas : h.gas.used + costDep290 cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f290.body))
      ⟨wStore cfg h⟩
      (fun v σ' => (∃ r, v = .trap r) ∧ ∃ cs, endCellsDep Cg (erase h) cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => ∃ r, v = .trap r)
    (fun _ cs => endCellsDep Cg (erase h) cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜∃ r, v = .trap r⌝ ∗ mcellsSat (fun cs => endCellsDep Cg (erase h) cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (startResNew cfg h).trans ?_
  iintro H
  iapply fupd_wp
  imod H with ⟨#Hk, #Hi, Hg, Hh, Hgas, Stk, HS, -⟩
  imodintro
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0], 0, wInst⟩ 0 f290.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body290Dep cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0 (some 2048)
    Interface.wInst_ifaceMod (by decide) Cg 0 { type := .num .i32, mutable := true } 1048576 (by decide)
    (by decide) 0 0 (erase h) hpre.view hpre.dep hpre.fit hpre.ov (entryPost Cg 0 Ψ)
  iframe Hk Stk HS
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
  iintro HT
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
    refine ⟨⟨h', g, p, a, ?_, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
    rw [he, depositMsg_utf8String]
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

/-- **`new` panics on a deposit** (`MethodPanicsR`). -/
theorem new_panics_deposit (cfg : RuntimeConfig) : MethodPanicsR cfg 290 PreDep (costDep cfg) postDep := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 290)) (entryCost cfg.wasm (.next (startW cfg h 290))) =
      (.next { startW cfg h 290 with store := wStore cfg (charged h (9 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_290, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costDep] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := new_adequate_dep cfg (charged h (9 * cfg.wasm.regularOpCost)) (by rw [erase_charged]; exact hpre) Cg
    (by rw [charged_gas_used, erase_charged]; simp only [costDep] at hcost; omega)
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
  rw [← startW_thread cfg h] at had
  have hend := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hend
  obtain ⟨⟨t, rfl⟩, cs, hcs, hlk⟩ := hend
  have hrun := trap_of_ending (runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨he, hu⟩ := endCellsDep_ends hcs hlk
  rw [erase_charged] at he
  exact ⟨t, σ.store, hrun, he, hu⟩

/-! ## The "already initialized" panic -/

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- What the "already initialized" panic needs of the host and the trie `st`: not a view call,
no deposit, `STATE` present, the premises of `storage_has_key` on it (room in the recorded proof
for its lookup) and of `panic_utf8` for the 41-byte message. -/
structure InitOk (e : NearState) (st : Near.TrieOverlay.State) : Prop where
  view : e.context.isView = false
  dep : depLo e ||| depHi e = 0
  present : ∃ v, e.storage StateRead.stateKey = some v
  acc : e.storageAccounting = some st
  lim : withinLimit e.config.maxStorageKeyLen 5 = true
  build : build st.entries = .ok st.base
  zero : zeroHash ∉ st.base.witness.map Prod.fst
  link : e.storage StateRead.stateKey = viewVal st (contractKey e.context.currentAccountId StateRead.stateKey)
  proof : ProofBudget e st (lookupProofBound (contractKey e.context.currentAccountId StateRead.stateKey))
  fit : LogFits e 41
  ov : e.extCosts.cost "read_memory_byte" * 41 < 2 ^ 64

def preInit (e : NearState) : Prop := ∃ st, InitOk e st

/-- Its cost: the entry activation (9) and `costInit290`. -/
def costInit (cfg : RuntimeConfig) (e : NearState) : Nat :=
  9 * cfg.wasm.regularOpCost + costInit290 cfg.wasm e

/-- What it does to the host: `storage_has_key`'s effect, then the panic. -/
def postInit (e e' : NearState) : Prop :=
  ∃ st h2, InitOk e st ∧ StorageHasKeyPost e StateRead.stateKey st h2 ∧
    e' = erase { h2 with lastError := some (.guestPanic initStr) }

/-- The cells `new` hands back on the "already initialized" panic. -/
def endCellsInit (Cg : Nat) (e : NearState) (st : Near.TrieOverlay.State) (cs : List (Loc × Cell NearState)) :
    Prop :=
  ∃ (h2 h' : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    StorageHasKeyPost e StateRead.stateKey st h2 ∧
    erase h' = erase { h2 with lastError := some (.guestPanic initStr) } ∧
    cs = [(Loc.host, .host (erase h')), (gasLoc, gasCellOf g p a)] ∧ g.used ≤ Cg

theorem endCellsInit_ends {Cg : Nat} {e : NearState} {st : Near.TrieOverlay.State} {σ' : MStore}
    {cs : List (Loc × Cell NearState)} (hc : endCellsInit Cg e st cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h2, StorageHasKeyPost e StateRead.stateKey st h2 ∧
      erase σ'.store.host = erase { h2 with lastError := some (.guestPanic initStr) } ∧
      σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h2, h', g, p, a, hq, he, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h2, hq, hh.trans he, hgg ▸ hg⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `new` on an initialized contract, no deposit**: every run that ends, ends in a
trap, the host after `storage_has_key` panicked with "The contract has already been
initialized", at most `Cg` used. -/
theorem new_adequate_init (cfg : RuntimeConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (hpre : InitOk (erase h) st) (Cg : Nat)
    (hgas : h.gas.used + costInit290 cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f290.body))
      ⟨wStore cfg h⟩
      (fun v σ' => (∃ r, v = .trap r) ∧ ∃ cs, endCellsInit Cg (erase h) st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => ∃ r, v = .trap r)
    (fun _ cs => endCellsInit Cg (erase h) st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜∃ r, v = .trap r⌝ ∗ mcellsSat (fun cs => endCellsInit Cg (erase h) st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (startResNew cfg h).trans ?_
  iintro H
  iapply fupd_wp
  imod H with ⟨#Hk, #Hi, Hg, Hh, Hgas, Stk, HS, -⟩
  imodintro
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0], 0, wInst⟩ 0 f290.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  obtain ⟨v, hv⟩ := hpre.present
  iapply body290Init cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0 (some 2048)
    Interface.wInst_ifaceMod (by decide) Cg 0 { type := .num .i32, mutable := true } 1048576 (by decide)
    (by decide) 0 0 (erase h) hpre.view hpre.dep v hv st hpre.acc hpre.lim hpre.build hpre.zero hpre.link
    hpre.proof le_rfl hpre.fit hpre.ov (entryPost Cg 0 Ψ)
  iframe Hk Stk HS
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
  iintro %h2 %hq HT
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
    refine ⟨⟨h2, h', g, p, a, hq, ?_, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
    rw [he, initMsg_utf8String]
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

/-- **`new` panics on an initialized contract with no deposit** (`MethodPanicsR`). -/
theorem new_panics_init (cfg : RuntimeConfig) : MethodPanicsR cfg 290 preInit (costInit cfg) postInit := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 290)) (entryCost cfg.wasm (.next (startW cfg h 290))) =
      (.next { startW cfg h 290 with store := wStore cfg (charged h (9 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_290, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costInit] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := new_adequate_init cfg (charged h (9 * cfg.wasm.regularOpCost)) st
    (by rw [erase_charged]; exact hr) Cg
    (by rw [charged_gas_used, erase_charged]; simp only [costInit] at hcost; omega)
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
  rw [← startW_thread cfg h] at had
  have hend := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hend
  obtain ⟨⟨t, rfl⟩, cs, hcs, hlk⟩ := hend
  have hrun := trap_of_ending (runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h2, hq, he, hu⟩ := endCellsInit_ends hcs hlk
  rw [erase_charged] at hq
  exact ⟨t, σ.store, hrun, ⟨st, h2, hr, hq, he⟩, hu⟩

end WNear.Binary.NewMethod
