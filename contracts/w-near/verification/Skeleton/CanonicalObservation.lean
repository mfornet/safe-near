import Skeleton.CanonicalCost
import Skeleton.FundedObservation
import NearVM.MeteredHosts.StorageModelUsage

/-! Checked observations of the actual funded body over arbitrary canonical
storage. Original guest context is fixed; only internal budgets are enlarged. -/
namespace WNear.Skeleton.CanonicalObservation
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- The computed canonical post-state represents the independent model write. -/
theorem after_represents (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset) :
    StorageRepresentation.Represents (CanonicalBody.after ctx host).host (savedStorage raw ctx.args).toFinset := by
  have h := CanonicalBody.phase_represents ctx raw host hh hwf
  have hp := ((h.setStorage "k".toUTF8.toList ctx.args).invalidateIterators).applyCharges
    (postCharges (CanonicalBody.phase ctx host) "k".toUTF8.toList)
    (postCharges_burnsOnly _ _)
  have hf := hp.updateStorageUsage ctx.protocol.fees.numExtraBytesRecord "storage_write"
    (CanonicalBody.phase ctx host) (CanonicalBody.phase ctx host).mem (args 1 0 u64Max 0)
  rw [show (savedStorage raw ctx.args).toFinset = rawWrite raw.toFinset "k".toUTF8.toList ctx.args
    from rawWrite_toFinset raw _ _]
  simpa only [CanonicalBody.after, finished, written] using hf

/-- Exact storage usage for both insertion and replacement, with explicit
native-width room and credits for the actual local storage call. -/
theorem after_usage (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hnodes : ctx.trie.NonzeroNodes) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hc : host.gas.Credits (successBudget ctx.protocol (CanonicalBody.bodyStore ctx host)
      (CanonicalBody.after ctx host) (CanonicalBody.cost ctx host) 0))
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64) :
    (CanonicalBody.after ctx host).host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage raw ctx.args).toFinset := by
  have hs := StorageCredits.body_storage ctx.protocol (CanonicalBody.bodyStore ctx host)
    (CanonicalBody.after ctx host) (CanonicalBody.cost ctx host) 0
    (by simpa only [CanonicalBody.bodyStore, FundedEmpty.bodyStore, initialized_host] using hc)
  have hi := CanonicalBody.invoke ctx raw host _ hh hwf hnodes hpages hkey hvalue
    (by simpa only [CanonicalBody.before, FundedEmpty.before] using hs) hproof
  have hnative : ctx.storageUsage < 2 ^ 64 := by omega
  have hu : (CanonicalBody.phase ctx host).host.context.storageUsage.toNat = ctx.storageUsage := by
    rw [CanonicalBody.phase_usage ctx raw host hh, UInt64.toNat_ofNat_of_lt' hnative]
  have hrep := CanonicalBody.phase_represents ctx raw host hh hwf
  have hge : storageUsageOf ctx.protocol raw.toFinset ≤
      (CanonicalBody.phase ctx host).host.context.storageUsage.toNat := by rw [hu]; exact hwf.usage_ge
  have hmodel := StorageModelUsage.writeUsage_model ctx.protocol _ _ hrep hge "k".toUTF8.toList ctx.args
  have hwidth := StorageModelUsage.writeUsage_lt ctx.protocol.fees.numExtraBytesRecord
    (CanonicalBody.phase ctx host) "k".toUTF8.toList ctx.args
    (by simpa only [hu, show "k".toUTF8.toList.length = 1 by decide +kernel] using hroom)
  rw [hi.2.2.2.1, UInt64.toNat_ofNat_of_lt' hwidth, hmodel, hu]
  rw [show (savedStorage raw ctx.args).toFinset = rawWrite raw.toFinset "k".toUTF8.toList ctx.args
    from rawWrite_toFinset raw _ _]

theorem checked_body_matches (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hm : ModelSaveLimits ctx)
    (hnodes : ctx.trie.NonzeroNodes)
    (hc : host.gas.Credits (successBudget ctx.protocol (CanonicalBody.bodyStore ctx host)
      (CanonicalBody.after ctx host) (CanonicalBody.cost ctx host) 0))
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64) :
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
          (.done [] ((successResults ctx.protocol (CanonicalBody.bodyStore ctx host) (CanonicalBody.after ctx host)).finalStore
            ctx.protocol.wasm (CanonicalBody.bodyStore ctx host))) none))
      ((model gasBound).step ctx st ()) := by
  have hinput : host.context.input = ctx.args := hhost.input
  rw [FundedObservation.final_eq ctx raw host _ hinput]
  have hb := (FundedEmpty.before_resources ctx raw host hhost).1.fields
  have hf := CanonicalBody.after_frame ctx host
  have hlogs : (CanonicalBody.after ctx host).host.logs = [] := hf.logs.trans (congrArg NearState.logs hb)
  have hpromises : (CanonicalBody.after ctx host).host.promises = [] := hf.promises.trans (congrArg NearState.promises hb)
  have hbalance : (CanonicalBody.after ctx host).host.context.accountBalance = ctx.balance + ctx.attached := by
    have h := congrArg (fun ns : NearState => ns.context.accountBalance) hf.2
    have h' := congrArg (fun ns : NearState => ns.context.accountBalance) hb
    exact h.trans h'
  have hu := after_usage ctx raw host hhost hwf hnodes hpages hm.key hm.value hc hproof hroom
  have hstate := represented_storage_getD gasBound raw st hrepresented
  have hupdated : (savedStorage (st.getD []) ctx.args).toFinset = (savedStorage raw ctx.args).toFinset := by
    simp only [savedStorage, rawWrite_toFinset, hstate]
  have hr : StorageRepresentation.Represents (CanonicalBody.after ctx host).host
      (savedStorage (st.getD []) ctx.args).toFinset := by
    rw [hupdated]
    exact after_represents ctx raw host hhost hwf
  have husage : (CanonicalBody.after ctx host).host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol raw.toFinset +
        storageUsageOf ctx.protocol (savedStorage (st.getD []) ctx.args).toFinset := by
    rw [hupdated]
    exact hu
  obtain ⟨ha, _, _, hou, hob, hol, hrec, _⟩ := executionOutcome_fields ctx.protocol
    (Near.Boundary.toVMContext ctx) raw (CanonicalBody.after ctx host) _ hr hpromises hlogs
  have hv := executionOutcome_receiptsValid ctx.protocol (Near.Boundary.toVMContext ctx) raw
    (CanonicalBody.after ctx host) hpromises
  unfold Near.Boundary.observeChecked
  simp only [VMOutcome.checkReceipts, hv, ↓reduceIte, hrec, Near.Boundary.actionsIssue?, List.findSome?_nil,
    Near.checkVMReceipts, List.zipIdx_nil, List.forIn_nil, pure, Except.pure]
  change Matches (model gasBound) ctx raw.toFinset _ (modelStep ctx st ())
  have hdef : stakeDeficit ctx.protocol
      (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw (CanonicalBody.after ctx host))) none).storageUsage
      (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw
        (.done [] (executionFinal ctx.protocol (Near.Boundary.toVMContext ctx) raw (CanonicalBody.after ctx host))) none).balance
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
    exact executionOutcome_matches_success gasBound ctx raw (st.getD []) (CanonicalBody.after ctx host)
      hr hpromises hlogs hbalance husage (by
        rw [husage, hbalance]
        simpa only [saveStakeDeficit, hstate] using hz)



def referenceBudget (ctx : Context) (raw : Storage) (rest : Nat) : Nat :=
  burnSum (origin ctx raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + (CanonicalCost.saveCost ctx + rest))

def referenceHost (ctx : Context) (raw : Storage) (rest : Nat) : NearState :=
  StartupSimulation.active ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))

/-- The actual funded reference reaches the concrete normal body state for
any adequate structural fuel. Guest-visible context remains original. -/
theorem reference_run (ctx : Context) (raw : Storage) (rest fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hm : ModelSaveLimits ctx) (hfuel : 16 ≤ fuel)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hnodes : ctx.trie.NonzeroNodes)
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := referenceHost ctx raw rest
    StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel =
      (.done [] ((successResults ctx.protocol (CanonicalBody.bodyStore ctx host) (CanonicalBody.after ctx host)).finalStore
        ctx.protocol.wasm (CanonicalBody.bodyStore ctx host)), none) := by
  let host := referenceHost ctx raw rest
  have hh : PreEq (origin ctx raw) host :=
    (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hs := StartupSimulation.reference_startup_credits ctx raw (CanonicalCost.saveCost ctx + rest)
  have hc : host.gas.Credits (CanonicalCost.saveCost ctx + rest) := hs.2.2
  have hbound := CanonicalCost.budget_le ctx raw host rest hh hwf hnodes hpages hm.key hm.value
  have hw := CanonicalBody.body_success ctx raw host rest execLimits hh hwf hnodes hpages hm hread
    (hc.mono hbound) hproof
  obtain ⟨_, hp, _⟩ := hw.result
  have hr16 : runMetered ctx.protocol.wasm 16
      (StartupSimulation.body ctx.protocol (enlargeHost (origin ctx raw) (referenceBudget ctx raw rest))) =
      (.done [] ((successResults ctx.protocol (CanonicalBody.bodyStore ctx host) (CanonicalBody.after ctx host)).finalStore
        ctx.protocol.wasm (CanonicalBody.bodyStore ctx host)), none) := by
    apply Prod.ext
    · simpa only [StartupSimulation.body, host, referenceHost, entryConfig, CanonicalBody.bodyStore, FundedEmpty.bodyStore, preparedData] using hp.2.1
    · simpa only [StartupSimulation.body, host, referenceHost, entryConfig, CanonicalBody.bodyStore, FundedEmpty.bodyStore, preparedData] using hp.2.2
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
    (hnodes : ctx.trie.NonzeroNodes)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let result := StartupSimulation.reference ctx raw (referenceBudget ctx raw rest) fuel
    Matches (model gasBound) ctx raw.toFinset
      (Near.Boundary.observeChecked code.codeOf ctx raw
        (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2))
      ((model gasBound).step ctx st ()) := by
  have hr := reference_run ctx raw rest fuel hwf hpages hm hfuel hread hnodes hproof
  dsimp only
  rw [hr]
  have hh : PreEq (origin ctx raw) (referenceHost ctx raw rest) :=
    (PreEq.enlarged _ _).trans (StartupSimulation.active_preEq _ _)
  have hs := StartupSimulation.reference_startup_credits ctx raw (CanonicalCost.saveCost ctx + rest)
  have hc : (referenceHost ctx raw rest).gas.Credits (CanonicalCost.saveCost ctx + rest) := hs.2.2
  have hbound := CanonicalCost.budget_le ctx raw (referenceHost ctx raw rest) 0 hh hwf hnodes hpages hm.key hm.value
  have hbound' : successBudget ctx.protocol (CanonicalBody.bodyStore ctx (referenceHost ctx raw rest))
      (CanonicalBody.after ctx (referenceHost ctx raw rest)) (CanonicalBody.cost ctx (referenceHost ctx raw rest)) 0 ≤
      CanonicalCost.saveCost ctx + rest := by omega
  exact checked_body_matches gasBound ctx raw st (referenceHost ctx raw rest) hh hwf hrepresented
    hpages hm hnodes (hc.mono hbound') hproof hroom



end WNear.Skeleton.CanonicalObservation
