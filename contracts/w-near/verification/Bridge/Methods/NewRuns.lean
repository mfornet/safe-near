import Bridge.Methods.NewPanics
import Bridge.Methods.CodeNewS
import Bridge.Methods.EntryRet

/-!
# `new` (290) on an uninitialized contract: the run

* `startResNewS`: the start's resources, the success path's code (`codeNewS_of`) included.
* `new_adequate_ok`: adequacy of `body290New` (through `mwp_entryR`, the body ending in `return`).
* `new_runs`: `MethodRunsR cfg 290 (preNew extra) (costNew cfg) (postNew extra)`.
-/

namespace WNear.Binary.NewMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.InitialState WNear.Binary.NewBody
open WNear.Binary.FtTotalSupplyMethod (g0_pt mhostPt_erase runInitialized_finished runInitialized_err
  done_of_values)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.EnvGetters (depLo depHi)
open WNear.Binary.MeasureUsage (mKey mVal)
open Near.TrieOverlay

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
theorem startResNewS_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (codeNewP cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
        codeNewS cfg.fees.numExtraBytesRecord 0 2048 0 wInst id (some 2048) ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗
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
  ihave #HkS := codeNewS_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  imodintro
  iframe Hk HkS Hg Hh Hgas Stk HS HSS
  iunfold instPt
  iexact Hi

theorem startResNewS (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (codeNewP cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
        codeNewS cfg.fees.numExtraBytesRecord 0 2048 0 wInst id (some 2048) ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗
        mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        staticsNewP 0 0 id 0 0 ∗ staticsNewS 0 0 id 123 2048 memLen) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startResNewS_gen wDataMem_image cfg h))

end Res

/-! ## What the success path needs -/

/-- What the success path needs of the host and the trie `st`, with `x` extra bytes per record:
not a view call, no deposit, `STATE` and the dummy record absent, the accounting a canonical trie
linked to the storage with room in the recorded proof for the four storage calls, the limits, and
room in the usage counter. -/
structure NewOk (x : Nat) (e : NearState) (st : Near.TrieOverlay.State) : Prop where
  view : e.context.isView = false
  dep : depLo e ||| depHi e = 0
  absent : e.storage StateRead.stateKey = none
  absentM : e.storage mKey = none
  acc : e.storageAccounting = some st
  canon : Canon st
  link : StorageLink e st
  proof : ProofBudget e st (lookupProofBound (contractKey e.context.currentAccountId StateRead.stateKey) +
      (writeProofCost (contractKey e.context.currentAccountId mKey) none +
        removeProofCost (contractKey e.context.currentAccountId mKey) (some mVal)) +
      writeProofCost (contractKey e.context.currentAccountId StateRead.stateKey) none)
  lim5 : withinLimit e.config.maxStorageKeyLen 5 = true
  lim69 : withinLimit e.config.maxStorageKeyLen 69 = true
  vlim16 : withinLimit e.config.maxStorageValueLen 16 = true
  vlim29 : withinLimit e.config.maxStorageValueLen 29 = true
  reg : withinLimit e.config.maxRegisterLen 16 = true
  usage : e.context.storageUsage.toNat + (85 + x) < 2 ^ 64

def preNew (x : Nat) (e : NearState) : Prop := ∃ st, NewOk x e st

/-- Its cost: the entry activation (9) and `costNew290`. -/
def costNew (cfg : RuntimeConfig) (e : NearState) : Nat :=
  9 * cfg.wasm.regularOpCost + costNew290 cfg.wasm e

/-- What it does to the host: the chain of `NewPost`. -/
def postNew (x : Nat) (e e' : NearState) : Prop := ∃ h4, NewPost x e h4 ∧ e' = erase h4

/-! ## Adequacy -/

/-- The cells `new` hands back on its success path. -/
def endCellsNew (Cg x : Nat) (e : NearState) (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h4 : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    NewPost x e h4 ∧ cs = [(Loc.host, .host (erase h4)), (gasLoc, gasCellOf g p a)] ∧ g.used ≤ Cg

theorem endCellsNew_ends {Cg x : Nat} {e : NearState} {σ' : MStore} {cs : List (Loc × Cell NearState)}
    (hc : endCellsNew Cg x e cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h4, NewPost x e h4 ∧ erase σ'.store.host = erase h4 ∧ σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h4, g, p, a, hq, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h4, hq, hh, hgg ▸ hg⟩

theorem heapRoom_memLen : LookupMapOps.HeapRoomK 9 memLen 2048 := by
  unfold LookupMapOps.HeapRoomK memLen; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `new` on an uninitialized contract, no deposit**: every run that ends, ends with
no values, the host as `NewPost`, at most `Cg` used. -/
theorem new_adequate_ok (cfg : RuntimeConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (hpre : NewOk cfg.fees.numExtraBytesRecord (erase h) st) (Cg : Nat)
    (hgas : h.gas.used + costNew290 cfg.wasm (erase h) ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f290.body))
      ⟨wStore cfg h⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, endCellsNew Cg cfg.fees.numExtraBytesRecord (erase h) cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => v = .values [])
    (fun _ cs => endCellsNew Cg cfg.fees.numExtraBytesRecord (erase h) cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => endCellsNew Cg cfg.fees.numExtraBytesRecord (erase h) cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (startResNewS cfg h).trans ?_
  iintro H
  iapply fupd_wp
  imod H with ⟨#Hk, #HkS, #Hi, Hg, Hh, Hgas, Stk, HS, HSS⟩
  imodintro
  iapply mwp_entryR cfg.wasm execLimits ⟨#[.i32 0], 0, wInst⟩ 0 f290.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body290New cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0 (some 2048)
    Interface.wInst_ifaceMod (by decide) Cg 0 { type := .num .i32, mutable := true } 1048576 (by decide)
    (by decide) 0 0 123 2048 memLen heapRoom_memLen (erase h) hpre.view hpre.dep hpre.absent hpre.absentM st
    hpre.acc hpre.canon hpre.link hpre.proof le_rfl hpre.lim5 hpre.lim69 hpre.vlim16 hpre.vlim29 hpre.reg
    hpre.usage (entryPostR cfg.wasm Cg 0 Ψ)
  iframe Hk HkS Stk HS HSS
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
  iintro %h4 %hq Hc - Hh
  simp only [entryPostR]
  isplitr
  · ipureintro; rfl
  iexists 0
  iframe Hc
  iintro Hc
  isplitr
  · ipureintro; rfl
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, %a, Hg', %hg⟩
  iexists [(Loc.host, Cell.host (erase h4)), (gasLoc, gasCellOf g p a)]
  isplitr
  · ipureintro
    exact ⟨⟨h4, g, p, a, hq, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
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

/-- **`new` runs on an uninitialized contract with no deposit** (`MethodRunsR`). -/
theorem new_runs (cfg : RuntimeConfig) :
    MethodRunsR cfg 290 (preNew cfg.fees.numExtraBytesRecord) (costNew cfg) (postNew cfg.fees.numExtraBytesRecord) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 290)) (entryCost cfg.wasm (.next (startW cfg h 290))) =
      (.next { startW cfg h 290 with store := wStore cfg (charged h (9 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_290, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [costNew] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := new_adequate_ok cfg (charged h (9 * cfg.wasm.regularOpCost)) st
    (by rw [erase_charged]; exact hr) Cg
    (by rw [charged_gas_used, erase_charged]; simp only [costNew] at hcost; omega)
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
  rw [← startW_thread cfg h] at had
  have hend := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hend
  obtain ⟨rfl, cs, hcs, hlk⟩ := hend
  have hrun := done_of_values (runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h4, hq, he, hu⟩ := endCellsNew_ends hcs hlk
  rw [erase_charged] at hq
  exact ⟨σ.store, hrun, ⟨h4, hq, he⟩, hu⟩

end WNear.Binary.NewMethod
