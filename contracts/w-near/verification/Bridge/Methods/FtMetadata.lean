import Bridge.Methods.Code309
import Bridge.Methods.FtMetadataUninit
import Bridge.Methods.StorageBalanceBounds

/-!
# `ft_metadata` (309) on an initialized contract: the method, from its run to the clauses of `Refines`

As `Methods/StorageBalanceBounds.lean` for 306, with `body309` and the code `code309`:

* `startRes`: the resources `body309` starts from (`code309_of`, `staticsRes309P`, 1024 bytes of
  stack).
* `fm_adequate`: adequacy of `body309` from the store after the entry activation.
* `ftMetadata_runs`: `MethodRunsR cfg 309 pre (cost cfg S) (post S)`.
* `ftMetadata_refines`: `method_refines_callR` for a call to `ft_metadata`.
-/

namespace WNear.Binary.FtMetadataMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupply WNear.Binary.U128View WNear.Binary.FtMetadataBody
  WNear.Binary.InitialState WNear.Binary.FtTotalSupplyMethod
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.MetadataFields (metaJson)

/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The resources of the start on an initialized contract, for `code309`. -/
theorem startRes_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code309 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047552 1024 ∗
        statics309 0 0 id 0 0 123 1051836 2048 memLen) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := tableOf $$ HT
  ihave HS := staticsRes309P hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  icases HS with ⟨Stk, HS, -⟩
  ihave #Hk := code309_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  imodintro
  iframe Hk Hg Hh Hgas Stk HS
  iunfold instPt
  iexact Hi

theorem startRes (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (code309 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047552 1024 ∗
        statics309 0 0 id 0 0 123 1051836 2048 memLen) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startRes_gen wDataMem_image cfg h))

end Res

/-! ## Adequacy -/

/-- The cells `ft_metadata` hands back, from the host `e` reading the model state `S`: the host
after `storage_read` (`h1`) with the metadata's JSON returned, and the gas counter within `Cg`. -/
def endCells (Cg : Nat) (e : NearState) (st : Near.TrieOverlay.State)
    (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h1 : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    StorageReadPost e StateRead.stateKey 0 st h1 ∧
    cs = [(Loc.host, .host (erase (h1.selectReturnValue metaJson))), (gasLoc, gasCellOf g p a)] ∧ g.used ≤ Cg

theorem endCells_ends {Cg : Nat} {e : NearState} {st : Near.TrieOverlay.State} {σ' : MStore}
    {cs : List (Loc × Cell NearState)} (hc : endCells Cg e st cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h1, StorageReadPost e StateRead.stateKey 0 st h1 ∧
      erase σ'.store.host = erase (h1.selectReturnValue metaJson) ∧ σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h1, g, p, a, hq, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h1, hq, hh, hgg ▸ hg⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `ft_metadata`**, from the store after the entry activation (host `h`): every run
that ends, ends with no values, the host after `storage_read` with the metadata's JSON returned,
and at most `Cg` used. -/
theorem fm_adequate (cfg : RuntimeConfig)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) (hr : ReadOkV (erase h) S st metaJson)
    (Cg : Nat) (hgas : h.gas.used + cost309 cfg.wasm (erase h) S ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f309.body))
      ⟨wStore cfg h⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, endCells Cg (erase h) st cs ∧ ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => v = .values [])
    (fun _ cs => endCells Cg (erase h) st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => endCells Cg (erase h) st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (startRes cfg h).trans ?_
  iintro H
  iapply fupd_wp
  imod H with ⟨#Hk, #Hi, Hg, Hh, Hgas, Stk, HS⟩
  imodintro
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0, .i32 0, .i32 0], 0, wInst⟩ 0 f309.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047552) (b := (1048576 : UInt32).toNat - 1024) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body309 cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0 Interface.wInst_ifaceMod
    (by decide) Cg 0 { type := .num .i32, mutable := true } 1048576 (by decide) (by decide) 0 0 123 1051836
    2048 memLen ⟨by decide, by decide, by decide, by decide⟩ (erase h) S st hr (entryPost Cg 0 Ψ)
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
  iintro %h1 %hq Hc Hg Hh
  simp only [entryPost]
  isplitr
  · ipureintro; rfl
  iexists 0
  iframe Hc
  iintro Hc
  isplitr
  · ipureintro; rfl
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, %a, Hg', %hg⟩
  iexists [(Loc.host, Cell.host (erase (h1.selectReturnValue metaJson))), (gasLoc, gasCellOf g p a)]
  isplitr
  · ipureintro
    exact ⟨⟨h1, g, p, a, hq, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
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

/-- What `ft_metadata` needs of the host: it reads the model state `S` (`ReadOkV`, the return
limit for the 138 bytes). -/
def pre (S : WNear.State) (e : NearState) : Prop := ∃ st, ReadOkV e S st metaJson

/-- Its cost: the entry activation (10) and `cost309`. -/
noncomputable def cost (cfg : RuntimeConfig) (S : WNear.State) (e : NearState) : Nat :=
  10 * cfg.wasm.regularOpCost + cost309 cfg.wasm e S

/-- What it does to the host: `storage_read`'s effect, then the metadata's JSON as the return
data. -/
def post (S : WNear.State) (e e' : NearState) : Prop :=
  ∃ st h1, ReadOkV e S st metaJson ∧ StorageReadPost e StateRead.stateKey 0 st h1 ∧
    e' = erase (h1.selectReturnValue metaJson)

/-- **`ft_metadata` runs** (`MethodRunsR`) on an initialized contract. -/
theorem ftMetadata_runs (cfg : RuntimeConfig) (S : WNear.State) :
    MethodRunsR cfg 309 (pre S) (cost cfg S) (post S) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 309)) (entryCost cfg.wasm (.next (startW cfg h 309))) =
      (.next { startW cfg h 309 with store := wStore cfg (charged h (10 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_309, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [cost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := fm_adequate cfg (charged h (10 * cfg.wasm.regularOpCost)) S st hr Cg
    (by rw [charged_gas_used, erase_charged]; simp only [cost] at hcost; omega)
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
  rw [← startW_thread cfg h] at had
  have hend := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hend
  obtain ⟨rfl, cs, hcs, hlk⟩ := hend
  have hrun := done_of_values (runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h1, hq, he, hu⟩ := endCells_ends hcs hlk
  exact ⟨σ.store, hrun, ⟨st, h1, hr, hq, he⟩, hu⟩

/-! ## The clauses of `Refines` -/

/-- The hosts `post` allows created no promises when the initial one did not. -/
theorem post_noPromises {S : WNear.State} {e e' : NearState} (hp : post S e e') (h0 : NoPromises e) :
    NoPromises e' := by
  obtain ⟨st, h1, -, ⟨s2, -, he⟩, rfl⟩ := hp
  have hregs : ∀ (x : NearState) (v : Option (List UInt8)),
      (storageReadRegs x 0 v).promises = x.promises ∧ (storageReadRegs x 0 v).gasWeights = x.gasWeights := by
    intro x v; unfold storageReadRegs; split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have hpr : h1.promises = e.promises :=
    (erase_field he NearState.promises fun _ => rfl).trans (hregs _ _).1
  have hgw : h1.gasWeights = e.gasWeights :=
    (erase_field he NearState.gasWeights fun _ => rfl).trans (hregs _ _).2
  exact ⟨by simp [erase, NearState.selectReturnValue, hpr, h0.promises],
    by simp [erase, NearState.selectReturnValue],
    by simp [erase, NearState.selectReturnValue, hgw, h0.weights]⟩

open NearInterface ContractModel in
/-- **The clauses of `Refines` for a call to `ft_metadata`** (function 309), from
`ftMetadata_runs`, against the model's step. -/
theorem ftMetadata_refines (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option M.State) (ctx : Context) (c : M.Call) (S : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_metadata")
    (hpre : ctx.ProofRoom (M.proofBound ctx st c) → pre S (erase (hostOf ctx raw)))
    (hpreP : pre S (eraseP (hostOf ctx raw)))
    (hag : ∀ e, post S (erase (hostOf ctx raw)) e → AgreesWith M ctx raw e (M.step ctx st c))
    (hagP : ∀ e, post S (eraseP (hostOf ctx raw)) e → AgreesWith M ctx raw e (M.step ctx st c))
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) + cost ctx.protocol S (erase (hostOf ctx raw)) ≤
      M.gas ctx st c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := M.step ctx st c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (M.gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom (M.proofBound ctx st c) →
      Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) :=
  method_refines_callR M size codeOf raw st ctx c (pre S) (cost ctx.protocol S) (post S) hp hwf
    (by rw [hm]; decide) (by rw [hm]; exact export_309) funcType_309 (by decide) (by decide)
    (ftMetadata_runs ctx.protocol S) hpre hpreP
    (fun e he => post_noPromises (e := erase (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    (fun e he => post_noPromises (e := eraseP (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩) hag hagP hbound

end WNear.Binary.FtMetadataMethod
