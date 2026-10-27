import Skeleton.FundedEmpty
import Skeleton.StartupSimulation
import Skeleton.ReceiptSimulation
import NearRuntime.BudgetObservation

/-! Checked observations of the actual funded reference, with original
VMContext and explicit protocol arithmetic room. -/
namespace WNear.Skeleton.FundedObservation
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation FundedEmpty
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- Once storage has committed its host and memory, the suffix is independent
of the initial counter. Only the original input is used to select the return. -/
theorem final_eq (ctx : Context) (raw : Storage) (host : NearState)
    (storage : HostStore NearState) (hinput : host.context.input = ctx.args) :
    (successResults ctx.protocol (bodyStore ctx host) storage).finalStore ctx.protocol.wasm (bodyStore ctx host) =
      executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw storage := by
  have hb : successReturnBefore ctx.protocol (bodyStore ctx host) storage =
      successReturnBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) storage := by
    unfold successReturnBefore successLogBefore successStorageBefore successInputBefore successInputAfter
      successLogAfter bodyStore executionStore
    rfl
  simp only [HostResults.finalStore, successResults_beforeReturn, successResults_returned,
    executionFinal, hb]
  have hi : (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw).host.context.input = ctx.args :=
    executionActive_input _ _ _
  simp only [bodyStore, initialized_host, hinput, hi]

/-- Original raw representation is retained at arbitrary framed storage entry. -/
theorem before_represents (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset) :
    StorageRepresentation.Represents (FundedEmpty.before ctx host).host raw.toFinset := by
  have hb := (before_resources ctx raw host hhost).1.fields
  have hr := StorageRepresentation.toNearState_represents ctx.protocol (Near.Boundary.toVMContext ctx)
    raw raw.toFinset rfl hwf.raw_keys_unique
  have hk := congrArg NearState.storageKeys hb
  change (FundedEmpty.before ctx host).host.storageKeys = (origin ctx raw).storageKeys at hk
  constructor
  · intro key value
    rw [hb.storage]
    exact hr.lookup key value
  · intro key value hm
    rw [hk]
    exact hr.coverage key value hm

private theorem finished_rep (extra : Nat) (b : HostStore NearState)
    (raw : RawStorage) (h : StorageRepresentation.Represents b.host raw) (key value : Near.Bytes) :
    let p := (applyCharges (written b key value).host (postCharges b key)).1
    StorageRepresentation.Represents (finished extra b 1 0 u64Max 0 key value p).host (rawWrite raw key value) := by
  have hp := ((h.setStorage key value).invalidateIterators).applyCharges
    (postCharges b key) (postCharges_burnsOnly b key)
  exact hp.updateStorageUsage extra "storage_write" b b.mem (args 1 0 u64Max 0)

/-- The actual computed storage post-state represents the model write. -/
theorem after_represents (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset) :
    StorageRepresentation.Represents (FundedEmpty.after ctx host).host (savedStorage raw ctx.args).toFinset := by
  have hp := (before_represents ctx raw host hhost hwf).applyCharges (preCharges ctx host)
    (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0)
  rw [show (applyCharges (FundedEmpty.before ctx host).host (preCharges ctx host)).1 = paid ctx host
    by unfold paid; rfl] at hp
  have hpre := hp.paidStore (FundedEmpty.before ctx host)
  have hphase := hpre.prepared (Output.paidStore (FundedEmpty.before ctx host) (paid ctx host))
    (applyCharges (accounted (Output.paidStore (FundedEmpty.before ctx host) (paid ctx host)) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    (ctx.trie.set (Near.TrieOverlay.contractKey (paid ctx host).context.currentAccountId "k".toUTF8.toList) ctx.args)
  have hf := finished_rep ctx.protocol.fees.numExtraBytesRecord _ raw.toFinset hphase "k".toUTF8.toList ctx.args
  rw [show (savedStorage raw ctx.args).toFinset = rawWrite raw.toFinset "k".toUTF8.toList ctx.args
    from rawWrite_toFinset raw _ _]
  simpa only [FundedEmpty.after, FundedEmpty.phase] using hf


private theorem prepared_key (ctx : Context) (raw : Storage) (b : HostStore NearState)
    (hm : b.mem = preparedData ctx.protocol) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg b 0 1 = some "k".toUTF8.toList := by
  let ref := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  have he : b.mem = ref.mem := hm.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw).symm
  calc
    getMemOrReg b 0 1 = getMemOrReg ref 0 1 := by
      simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte, he]
    _ = _ := emptyPaid_key ctx raw hpages

/-- The generic funded post-write usage agrees with the independent model;
its native-width hypothesis is stated on original context data. -/
theorem after_usage (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64) :
    (FundedEmpty.after ctx host).host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage raw ctx.args).toFinset := by
  have hb := before_resources ctx raw host hhost
  have hp : PreEq (origin ctx raw) (paid ctx host) := by
    simpa only [paid] using hb.1.fields.trans (PreEq.charges (FundedEmpty.before ctx host).host
      (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0))
  have hr : StorageOverlay.Represents (paid ctx host) ctx raw := by
    refine ⟨hp.current, ?_⟩
    intro key
    rw [hp.storage]
    rfl
  have hn0 := StorageEmpty.storage_none (Output.paidStore (FundedEmpty.before ctx host) (paid ctx host))
    ctx raw.toFinset hwf raw rfl ⟨hr.1, hr.2⟩ "k".toUTF8.toList hentries hselected
  have hn : (FundedEmpty.phase ctx host).host.storage "k".toUTF8.toList = none := by
    simpa only [FundedEmpty.phase, prepared, Output.paidStore] using hn0
  have hu : (FundedEmpty.phase ctx host).host.context.storageUsage = UInt64.ofNat ctx.storageUsage := by
    have h := congrArg (fun ns : NearState => ns.context.storageUsage) hp
    change (paid ctx host).context.storageUsage = UInt64.ofNat ctx.storageUsage at h
    simpa only [FundedEmpty.phase, prepared, Output.paidStore] using h
  have hkey := prepared_key ctx raw (FundedEmpty.phase ctx host)
    (by simpa only [FundedEmpty.phase, prepared, Output.paidStore] using hb.1.memory) hpages
  have hpost : postCharges (FundedEmpty.phase ctx host) "k".toUTF8.toList = [] := by
    simp only [postCharges, hn]
  have hcharge : applyCharges (written (FundedEmpty.phase ctx host) "k".toUTF8.toList ctx.args).host
      (postCharges (FundedEmpty.phase ctx host) "k".toUTF8.toList) =
      ((applyCharges (written (FundedEmpty.phase ctx host) "k".toUTF8.toList ctx.args).host
        (postCharges (FundedEmpty.phase ctx host) "k".toUTF8.toList)).1, none) := by
    rw [hpost]
    rfl
  have husageRoom : ctx.storageUsage < 2 ^ 64 := by omega
  have hw : writeUsage ctx.protocol.fees.numExtraBytesRecord (FundedEmpty.phase ctx host) "k".toUTF8.toList ctx.args =
      ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord := by
    simp only [writeUsage, hn, hu, UInt64.toNat_ofNat_of_lt' husageRoom]
    rw [show "k".toUTF8.toList.length = 1 by decide +kernel]
  have hf := finished_usage_toNat ctx.protocol.fees.numExtraBytesRecord (FundedEmpty.phase ctx host)
    1 0 u64Max 0 "k".toUTF8.toList ctx.args _ hkey hcharge (by rw [hw]; exact hroom)
  have ha : (FundedEmpty.after ctx host).host.context.storageUsage.toNat =
      ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord := by
    simpa only [FundedEmpty.after, hw] using hf
  have hbeforeNone := StorageEmpty.storage_none (FundedEmpty.before ctx host) ctx raw.toFinset hwf raw rfl
    hb.1.represents "k".toUTF8.toList hentries hselected
  have hrep := before_represents ctx raw host hhost hwf
  have habsent : ∀ old, ("k".toUTF8.toList, old) ∉ raw.toFinset := by
    intro old he
    have h := (hrep.lookup _ old).mpr he
    rw [hbeforeNone] at h
    cases h
  have hk : "k".toUTF8.toList.length = 1 := by decide +kernel
  have hformula := write_usage_fresh_toNat ctx.protocol raw.toFinset ctx.storageUsage "k".toUTF8.toList ctx.args
    hwf.usage_ge habsent (by simpa only [hk] using hroom)
  rw [ha]
  rw [show (savedStorage raw ctx.args).toFinset = rawWrite raw.toFinset "k".toUTF8.toList ctx.args from rawWrite_toFinset raw _ _]
  simpa only [hk, UInt64.toNat_ofNat_of_lt' hroom] using hformula


/-- Observing the computed funded body state agrees with the independent
model on both final stake outcomes. No gas sufficiency premise is used here. -/
theorem checked_body_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hm : ModelSaveLimits ctx)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64) :
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
          (.done [] ((successResults ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)).finalStore
            ctx.protocol.wasm (bodyStore ctx host))) none))
      ((model gasBound).step ctx st ()) := by
  have hinput : host.context.input = ctx.args := hhost.input
  rw [final_eq ctx raw host _ hinput]
  have hb := (before_resources ctx raw host hhost).1.fields
  have hf := after_frame ctx host
  have hlogs : (FundedEmpty.after ctx host).host.logs = [] := hf.logs.trans (congrArg NearState.logs hb)
  have hpromises : (FundedEmpty.after ctx host).host.promises = [] := hf.promises.trans (congrArg NearState.promises hb)
  have hbalance : (FundedEmpty.after ctx host).host.context.accountBalance = ctx.balance + ctx.attached := by
    have h := congrArg (fun ns : NearState => ns.context.accountBalance) hf.2
    have h' := congrArg (fun ns : NearState => ns.context.accountBalance) hb
    exact h.trans h'
  have hu := after_usage ctx raw host hhost hwf hpages hentries hselected hroom
  have hstate := represented_storage_getD gasBound raw st hrepresented
  have hupdated : (savedStorage (st.getD []) ctx.args).toFinset = (savedStorage raw ctx.args).toFinset := by
    simp only [savedStorage, rawWrite_toFinset, hstate]
  have hr : StorageRepresentation.Represents (FundedEmpty.after ctx host).host
      (savedStorage (st.getD []) ctx.args).toFinset := by
    rw [hupdated]
    exact after_represents ctx raw host hhost hwf
  have husage : (FundedEmpty.after ctx host).host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage (st.getD []) ctx.args).toFinset := by
    rw [hupdated]
    exact hu
  obtain ⟨ha, _, _, hou, hob, hol, hrec, _⟩ := executionOutcome_fields ctx.protocol
    (Near.Boundary.toVMContext ctx) raw (FundedEmpty.after ctx host) _ hr hpromises hlogs
  have hv := executionOutcome_receiptsValid ctx.protocol (Near.Boundary.toVMContext ctx) raw
    (FundedEmpty.after ctx host) hpromises
  unfold Near.Boundary.observeChecked
  simp only [VMOutcome.checkReceipts, hv, ↓reduceIte, hrec, Near.Boundary.actionsIssue?, List.findSome?_nil,
    Near.checkVMReceipts, List.zipIdx_nil, List.forIn_nil, pure, Except.pure]
  change Matches (model gasBound) ctx raw.toFinset _ (modelStep ctx st ())
  have hdef : stakeDeficit ctx.protocol
      (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw (FundedEmpty.after ctx host))) none).storageUsage
      (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw (FundedEmpty.after ctx host))) none).balance
      ctx.locked = saveStakeDeficit ctx (st.getD []) := by
    rw [hou, hob, husage, hbalance]
    simp only [saveStakeDeficit, hstate]
  by_cases hd : 0 < saveStakeDeficit ctx (st.getD [])
  · rw [modelStep_save_stakeFailure ctx st hm hd]
    have h := Near.Boundary.observe_matches_stakeFailure (M := model gasBound) (ctx := ctx)
      (storage := raw) (issue := none) (receiptError := none) ha rfl rfl
      (by rw [hdef]; exact hd) hol
    rw [hdef] at h
    exact h
  · have hz : saveStakeDeficit ctx (st.getD []) = 0 := by omega
    rw [modelStep_save_success ctx st hm hz]
    exact executionOutcome_matches_success gasBound ctx raw (st.getD []) (FundedEmpty.after ctx host)
      hr hpromises hlogs hbalance husage (by
        rw [husage, hbalance]
        simpa only [saveStakeDeficit, hstate] using hz)


/-- A generous auxiliary reservation covers actual startup and a full body.
It does not impose any condition on the original context's gasLimit. -/
def referenceBudget (ctx : Context) (raw : Storage) (rest : Nat) : Nat :=
  burnSum (origin ctx raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + (saveEmptyCost ctx + rest))

def referenceHost (ctx : Context) (raw : Storage) (rest : Nat) : NearState :=
  StartupSimulation.active ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))

/-- The actual funded reference reaches the concrete normal body state for
any adequate structural fuel. Guest-visible context remains original. -/
theorem reference_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hm : ModelSaveLimits ctx) (hfuel : 16 ≤ fuel)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.done [] ((successResults ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)).finalStore
        ctx.protocol.wasm (bodyStore ctx host)), none) := by
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host :=
    (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hs := StartupSimulation.reference_startup_credits ctx raw (saveEmptyCost ctx + rest)
  have hc : host.gas.Credits (saveEmptyCost ctx + rest) := hs.2.2
  have hbound := budget_le ctx raw host rest hh hpages hm.key hm.value
  have hw := body_success ctx raw host rest execLimits hh hwf hpages hm hread hentries hselected
    (hc.mono hbound) hproof
  obtain ⟨_, hp, _⟩ := hw.result
  have hr16 : runMetered ctx.protocol.wasm 16
      (StartupSimulation.body ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))) =
      (.done [] ((successResults ctx.protocol (bodyStore ctx host) (FundedEmpty.after ctx host)).finalStore
        ctx.protocol.wasm (bodyStore ctx host)), none) := by
    apply Prod.ext
    · simpa only [StartupSimulation.body, host, referenceHost, entryConfig, bodyStore, preparedData] using hp.2.1
    · simpa only [StartupSimulation.body, host, referenceHost, entryConfig, bodyStore, preparedData] using hp.2.2
  have hextra := runMetered_extra_fuel ctx.protocol.wasm 16
    (StartupSimulation.body ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))) (by rw [hr16]; simp) (fuel - 16)
  rw [show 16 + (fuel - 16) = fuel by omega] at hextra
  exact hextra.trans hr16

/-- Checked observation of the actual auxiliary reference matches the
independent model for accepted VM limits and either stake outcome. This has
no original-gas sufficiency premise and no whole-execution callback. -/
theorem reference_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hm : ModelSaveLimits ctx) (hfuel : 16 ≤ fuel)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2))
      ((model gasBound).step ctx st ()) := by
  have hr := reference_run ctx raw rest fuel hwf hpages hm hfuel hread hentries hselected hproof
  dsimp only
  rw [hr]
  have hh : PreEq (origin ctx raw) (referenceHost ctx raw rest) :=
    (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  exact checked_body_matches gasBound ctx raw st (referenceHost ctx raw rest) hh hwf hrepresented
    hpages hm hentries hselected hroom


private theorem matched_logs (M : ContractModel) (ctx : Context) (raw : RawStorage)
    (observed : Observation) (result : NearInterface.StepResult M.Panic M.State M.Ret M.Promise)
    (h : Matches M ctx raw observed result) : observed.logs = result.logs := by
  cases result with
  | ok out => exact h.2.2.2.2.1
  | error failure => exact h.2.2.2.2.1

/-- The actual lower-gas alternative of refinement for accepted VM limits on
the explicit empty-base slice. Any original gas budget either matches the model
or aborts out of gas with rollback and a prefix of the model's logs. -/
theorem execOn_matches_or_gas (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hmethod : ctx.method = "save") (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) ∨
    ((Near.Boundary.execOn code raw ctx).outcome = .error .outOfGas ∧
      RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      (Near.Boundary.execOn code raw ctx).logs <+: ((model gasBound).step ctx st ()).logs) := by
  have hhigh := reference_matches gasBound ctx raw st 0
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hwf hrepresented hp.positive hm
    (fuelFor_save _ _) hread hentries hselected hroom hproof
  change Matches (model gasBound) ctx raw.toFinset
    (ReceiptSimulation.referenceObservation ctx raw (referenceBudget ctx raw 0)) ((model gasBound).step ctx st ()) at hhigh
  have hl := matched_logs (model gasBound) ctx raw.toFinset _ _ hhigh
  have hr := ReceiptSimulation.execOn_replay ctx raw (referenceBudget ctx raw 0) hmethod hwf
    hp.positive hp.minmax hp.maximum hp.types hp.functions hentries hselected hproof
  rcases hr with he | hg
  · left
    rw [he]
    exact hhigh
  · right
    rw [hl] at hg
    exact hg

end WNear.Skeleton.FundedObservation
