import Bridge.Methods.Code296
import Bridge.Methods.Relational
import Spec.Contract

/-!
# `ft_total_supply` (296): the method, from its run to the clauses of `Refines`

* `startRes`: from the cells of the instantiated store (`StartCells`), the resources `f296_spec`
  starts from: the code (`code296_of`), the instance, the stack pointer global (1048576), the
  host, the gas counter, the 736 bytes of stack below 1048576 and the statics (`staticsRes`).
* `ft_adequate`: adequacy of `body296` from the store after the entry activation (9
  `regular_op_cost`s): the run ends with no values, the host `h1.selectReturnValue (supplyJson S)`
  (`h1` the host after `storage_read`, `StorageReadPost`), at most `Cg` used.
* `ftTotalSupply_runs`: `MethodRunsR cfg 296 (pre S) (cost cfg S x96) (post S)`.
  `MethodRuns` (an exact `F`) cannot hold: `storage_read` leaves register 0 set and the
  accounting's caches updated (`StorageReadPost` only says some `s2` with the same data).
* `ftTotalSupply_refines`: `method_refines_callR` for a call to `ft_total_supply`.

Assumed (hypotheses): `ToVecAfterFree` (`to_vec` on a two-cell free list), the storage premises
(`ReadOk`: the recorded proof's room for the lookup (`ProofBudget`), the link through the overlay's view, no zero-hash witness), and,
for `Refines`, that the model's step agrees with every final host (`hag`).
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupply WNear.Binary.InitialState
open WNear.Binary.VecFromElem (stk)

/-! ## Runs that end (from the walking skeleton, `NearLogic.Examples.SkeletonRun`) -/

theorem runMetered_finished (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : (runMetered cfg fuel m).2 ≠ some (.executionIssue .fuelExhausted)) :
    ∃ e σ, resultCode cfg (runMetered cfg fuel m) = (.finished e, σ) := by
  induction fuel generalizing m with
  | zero =>
    cases m with
    | next c => exact absurd rfl h
    | done vs s => exact ⟨_, _, by rw [runMetered_done]; rfl⟩
    | trap r s => exact ⟨_, _, by rw [runMetered_trapped]; rfl⟩
  | succ fuel ih =>
    cases m with
    | done vs s => exact ⟨_, _, by rw [runMetered_done]; rfl⟩
    | trap r s => exact ⟨_, _, by rw [runMetered_trapped]; rfl⟩
    | next c =>
      unfold runMetered at h ⊢
      cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
      | some e => simp only [h1]; exact ⟨_, _, rfl⟩
      | none =>
        simp only [h1] at h ⊢
        cases h2 : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
            (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
              (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 with
        | some e => simp only [h2]; exact ⟨_, _, rfl⟩
        | none =>
          simp only [h2] at h ⊢
          exact ih _ h

theorem runInitialized_finished (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : (runInitialized cfg fuel m).2 ≠ some (.executionIssue .fuelExhausted)) :
    ∃ e σ, resultCode cfg (runInitialized cfg fuel m) = (.finished e, σ) := by
  unfold runInitialized at h ⊢
  simp only at h ⊢
  split
  · exact ⟨_, _, rfl⟩
  · rename_i h2
    rw [h2] at h
    exact runMetered_finished cfg fuel _ h


/-- `runMetered` reports nothing, a failed charge, or fuel exhaustion. -/
theorem runMetered_err (cfg : WasmConfig) (fuel : Nat) (m : Machine) :
    (runMetered cfg fuel m).2 = none ∨ (∃ e, (runMetered cfg fuel m).2 = some (.hostError e)) ∨
      (runMetered cfg fuel m).2 = some (.executionIssue .fuelExhausted) := by
  induction fuel generalizing m with
  | zero => cases m <;> simp [runMetered]
  | succ fuel ih =>
    cases m with
    | done vs s => rw [runMetered_done]; simp
    | trap r s => rw [runMetered_trapped]; simp
    | next c =>
      unfold runMetered
      cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
      | some e => simp [h1]
      | none =>
        simp only [h1]
        cases h2 : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
            (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
              (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 with
        | some e => simp [h2]
        | none => simp only [h2]; exact ih _

theorem runInitialized_err (cfg : WasmConfig) (fuel : Nat) (m : Machine) :
    (runInitialized cfg fuel m).2 = none ∨ (∃ e, (runInitialized cfg fuel m).2 = some (.hostError e)) ∨
      (runInitialized cfg fuel m).2 = some (.executionIssue .fuelExhausted) := by
  unfold runInitialized
  cases h : (chargeWasm m (entryCost cfg m)).2 with
  | some e => simp [h]
  | none => simp only [h]; exact runMetered_err cfg fuel _

/-- A run that ended with values, and did not exhaust its fuel, is done. -/
theorem done_of_values {cfg : WasmConfig} {r : Machine × Option FunctionCallError} {vs : List Value} {σ : MStore}
    (herr : r.2 = none ∨ (∃ e, r.2 = some (.hostError e)) ∨ r.2 = some (.executionIssue .fuelExhausted))
    (hfuel : r.2 ≠ some (.executionIssue .fuelExhausted))
    (h : resultCode cfg r = (.finished (.values vs), σ)) : r = (.done vs σ.store, none) := by
  obtain ⟨m, err⟩ := r
  simp only at herr hfuel
  rcases herr with rfl | ⟨e, rfl⟩ | rfl
  · cases m with
    | next c => simp [resultCode] at h
    | done vs' s => simp only [resultCode, Prod.mk.injEq, MCode.finished.injEq, Ending.values.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h; rfl
    | trap r s => simp [resultCode] at h
  · simp [resultCode] at h
  · exact absurd rfl hfuel


/-! ## The start's resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- **The resources of the start.** From the separated cells of the store (any memory with the
instantiated image), after making the functions, the instance and the memory limit persistent. -/
theorem startRes_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code296 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := tableOf $$ HT
  ihave HS := staticsRes hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  ihave #Hk := code296_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  imodintro
  iframe Hk Hg Hh Hgas HS
  iunfold instPt
  iexact Hi

theorem startRes (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (code296 cfg.fees.numExtraBytesRecord 0 wInst id 0 2048 ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ stk 0 1047840 736 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startRes_gen wDataMem_image cfg h))

end Res

/-! ## Adequacy -/

/-- The cells `ft_total_supply` hands back, from the host `e` reading the model state `S`: the
host after `storage_read` (`h1`) with the JSON of the total supply returned, and the gas counter
within `Cg`. -/
def endCells (Cg : Nat) (e : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h1 : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    StorageReadPost e StateRead.stateKey 0 st h1 ∧
    cs = [(Loc.host, .host (erase (h1.selectReturnValue (supplyJson S)))), (gasLoc, gasCellOf g p a)] ∧ g.used ≤ Cg

theorem endCells_ends {Cg : Nat} {e : NearState} {S : WNear.State} {st : Near.TrieOverlay.State} {σ' : MStore}
    {cs : List (Loc × Cell NearState)} (hc : endCells Cg e S st cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h1, StorageReadPost e StateRead.stateKey 0 st h1 ∧
      erase σ'.store.host = erase (h1.selectReturnValue (supplyJson S)) ∧ σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h1, g, p, a, hq, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h1, hq, hh, hgg ▸ hg⟩

theorem f296_frame : funcs[296 - 48]! = f296 := by kernel_rfl

theorem startW_thread (cfg : RuntimeConfig) (h : NearState) :
    (startW cfg h 296).thread = entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f296.body := by
  simp only [startW, wFrame, f296_frame, entryThread]
  rfl

theorem entryCost_296 (cfg : RuntimeConfig) (h : NearState) :
    entryCost cfg.wasm (.next (startW cfg h 296)) = 9 * cfg.wasm.regularOpCost := by
  have ht := startW_thread cfg h
  simp only [entryCost, Config.locals, ht, entryThread, activationGas]
  simp [ValType.default]

theorem g0_pt {GF : BundledGFunctors} [WasmGS NearState GF] :
    (0 ↦[wg] g0 : IProp GF) ⊢ 0 ↦[wg] ⟨{ type := .num .i32, mutable := true }, .i32 1048576⟩ := .rfl

theorem mhostPt_erase {GF : BundledGFunctors} [WasmGS NearState GF] (h : NearState) :
    mhostPt (GF := GF) (erase h) = mhostPt h := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Adequacy of `ft_total_supply`**, from the store after the entry activation (host `h`): every
run that ends, ends with no values, the host after `storage_read` with the JSON of the total
supply returned, and at most `Cg` used. -/
theorem ft_adequate (cfg : RuntimeConfig) (x96 : Nat) (H96 : ToVecAfterFree cfg.wasm execLimits x96)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State) (hr : ReadOk (erase h) S st) (Cg : Nat)
    (hgas : h.gas.used + cost296 cfg.wasm (erase h) S x96 ≤ Cg) (hC1 : Cg ≤ h.gas.maxBurnt)
    (hC2 : Cg ≤ h.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg.wasm execLimits (entryThread ⟨#[.i32 0], 0, wInst⟩ 0 f296.body))
      ⟨wStore cfg h⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, endCells Cg (erase h) S st cs ∧ ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => v = .values [])
    (fun _ cs => endCells Cg (erase h) S st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => endCells Cg (erase h) S st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (startRes cfg h).trans ?_
  iintro H
  iapply fupd_wp
  imod H with ⟨#Hk, #Hi, Hg, Hh, Hgas, Stk, HS⟩
  imodintro
  iapply mwp_entry cfg.wasm execLimits ⟨#[.i32 0], 0, wInst⟩ 0 f296.body Cg Ψ
  isplitr
  · iexact Hi
  ihave Stk := BorshFT.stkA (a := 1047840) (b := (1048576 : UInt32).toNat - 736) rfl $$ Stk
  rw [← mhostPt_erase h]
  iapply body296 cfg.wasm execLimits 0 cfg.fees.numExtraBytesRecord 0 wInst id 0 0 0 Interface.wInst_ifaceMod
    (by decide) x96 H96 Cg 0 { type := .num .i32, mutable := true } 1048576 (by decide) (by decide) 0 0 123 1051836 2048 memLen
    ⟨by decide, by decide, by decide, by decide⟩ (erase h) S st hr (entryPost Cg 0 Ψ)
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
  iexists [(Loc.host, Cell.host (erase (h1.selectReturnValue (supplyJson S)))), (gasLoc, gasCellOf g p a)]
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

/-- What `ft_total_supply` needs of the host: it reads the model state `S` (`ReadOk`). -/
def pre (S : WNear.State) (e : NearState) : Prop := ∃ st, ReadOk e S st

/-- Its cost: the entry activation (9) and `cost296`. -/
noncomputable def cost (cfg : RuntimeConfig) (S : WNear.State) (x96 : Nat) (e : NearState) : Nat :=
  9 * cfg.wasm.regularOpCost + cost296 cfg.wasm e S x96

/-- What it does to the host: `storage_read`'s effect (`StorageReadPost`: register 0, the
accounting's caches), then the JSON of the total supply as the return data. -/
def post (S : WNear.State) (e e' : NearState) : Prop :=
  ∃ st h1, ReadOk e S st ∧ StorageReadPost e StateRead.stateKey 0 st h1 ∧
    e' = erase (h1.selectReturnValue (supplyJson S))

/-- **`ft_total_supply` runs** (`MethodRunsR`), `to_vec` on a two-cell free list assumed. -/
theorem ftTotalSupply_runs (cfg : RuntimeConfig) (S : WNear.State) (x96 : Nat)
    (H96 : ToVecAfterFree cfg.wasm execLimits x96) :
    MethodRunsR cfg 296 (pre S) (cost cfg S x96) (post S) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  obtain ⟨st, hr⟩ := hpre
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 296)) (entryCost cfg.wasm (.next (startW cfg h 296))) =
      (.next { startW cfg h 296 with store := wStore cfg (charged h (9 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_296, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [cost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have had := ft_adequate cfg x96 H96 (charged h (9 * cfg.wasm.regularOpCost)) S st hr Cg
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
  obtain ⟨st, h1, -, ⟨s2, -, -, he⟩, rfl⟩ := hp
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

set_option maxRecDepth 100000 in
theorem funcType_296 : wNearModule.funcType? 296 = some { params := [], results := [] } := by kernel_rfl

theorem export_296 : wNearModule.exportFunc? "ft_total_supply" = some 296 := by decide

open NearInterface ContractModel in
/-- **The clauses of `Refines` for a call to `ft_total_supply`** (function 296), from
`ftTotalSupply_runs`, against the model's step. Hypotheses not discharged here: `H96` (`to_vec`
on a two-cell free list: the allocator's general walk), `hpre` (the host reads the model state
`S`: `ReadOk`, with the recorded proof's room for the lookup (`ProofBudget`) when the context has
room for the model's bound, the link through the overlay's view and canonical trie, no zero-hash witness,
the key/register/return limits), `hpreP` (the same of the host recording no
proof), `hag`, `hagP` (the model's step agrees with every final host: the return data
`supplyJson S`, storage, balance, usage, logs),
`hbound` (the gas bound covers loading and `cost`). -/
theorem ftTotalSupply_refines (M : ContractModel) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option M.State) (ctx : Context) (c : M.Call) (S : WNear.State) (x96 : Nat)
    (H96 : ToVecAfterFree ctx.protocol.wasm execLimits x96) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_total_supply")
    (hpre : ctx.ProofRoom (M.proofBound ctx st c) → pre S (erase (hostOf ctx raw)))
    (hpreP : pre S (eraseP (hostOf ctx raw)))
    (hag : ∀ e, post S (erase (hostOf ctx raw)) e → AgreesWith M ctx raw e (M.step ctx st c))
    (hagP : ∀ e, post S (eraseP (hostOf ctx raw)) e → AgreesWith M ctx raw e (M.step ctx st c))
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) + cost ctx.protocol S x96 (erase (hostOf ctx raw)) ≤
      M.gas ctx st c) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := M.step ctx st c
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (M.gas ctx st c ≤ ctx.gasLimit → ctx.ProofRoom (M.proofBound ctx st c) →
      Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
    (Matches M ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) :=
  method_refines_callR M size codeOf raw st ctx c (pre S) (cost ctx.protocol S x96) (post S) hp hwf
    (by rw [hm]; decide) (by rw [hm]; exact export_296) funcType_296 (by decide) (by decide)
    (ftTotalSupply_runs ctx.protocol S x96 H96) hpre hpreP
    (fun e he => post_noPromises (e := erase (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    (fun e he => post_noPromises (e := eraseP (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩) hag hagP hbound

open NearInterface ContractModel in
/-- `ftTotalSupply_refines` for the wNEAR model's step `(wnear cfg).step ctx st .ftTotalSupply`. -/
theorem ftTotalSupply_refines_wnear (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (S : WNear.State) (x96 : Nat)
    (H96 : ToVecAfterFree ctx.protocol.wasm execLimits x96) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_total_supply")
    (hpre : ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) → pre S (erase (hostOf ctx raw)))
    (hpreP : pre S (eraseP (hostOf ctx raw)))
    (hag : ∀ e, post S (erase (hostOf ctx raw)) e →
      AgreesWith (WNear.wnear cfg) ctx raw e ((WNear.wnear cfg).step ctx st .ftTotalSupply))
    (hagP : ∀ e, post S (eraseP (hostOf ctx raw)) e →
      AgreesWith (WNear.wnear cfg) ctx raw e ((WNear.wnear cfg).step ctx st .ftTotalSupply))
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) + cost ctx.protocol S x96 (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .ftTotalSupply) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .ftTotalSupply
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .ftTotalSupply ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx st .ftTotalSupply) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .ftTotalSupply) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) :=
  ftTotalSupply_refines (WNear.wnear cfg) size codeOf raw st ctx .ftTotalSupply S x96 H96 hp hwf hm hpre hpreP
    hag hagP hbound

end WNear.Binary.FtTotalSupplyMethod
