import Skeleton.FundedEmpty
import NearVM.MeteredHosts.StorageCanonical

/-!
# Accepted walking body over arbitrary canonical storage

The storage phase is the actual canonical lookup/dereference plan. No empty
base or selected-overlay condition is imposed; only the original WF, explicit
reserved-zero exclusion and recorded-proof acceptance remain.
-/
namespace WNear.Skeleton.CanonicalBody
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

abbrev bodyStore := FundedEmpty.bodyStore
abbrev before := FundedEmpty.before
abbrev preCharges := FundedEmpty.preCharges

@[irreducible] def paid (ctx : Context) (host : NearState) : NearState :=
  (applyCharges (before ctx host).host (preCharges ctx host)).1

def lookup (ctx : Context) (host : NearState) : StorageCanonical.LookupPlan :=
  StorageCanonical.plan ctx.trie
    (Near.TrieOverlay.contractKey (paid ctx host).context.currentAccountId "k".toUTF8.toList)

@[irreducible] def phase (ctx : Context) (host : NearState) : HostStore NearState :=
  (lookup ctx host).result (Output.paidStore (before ctx host) (paid ctx host)) ctx.trie "k".toUTF8.toList ctx.args

@[irreducible] def after (ctx : Context) (host : NearState) : HostStore NearState :=
  let b := phase ctx host
  let p := (applyCharges (written b "k".toUTF8.toList ctx.args).host (postCharges b "k".toUTF8.toList)).1
  finished ctx.protocol.fees.numExtraBytesRecord b 1 0 u64Max 0 "k".toUTF8.toList ctx.args p

def cost (ctx : Context) (host : NearState) : Nat :=
  burnSum (before ctx host).host.extCosts (preCharges ctx host) +
    burnSum (before ctx host).host.extCosts ((lookup ctx host).charges ctx.trie) +
    burnSum (before ctx host).host.extCosts (postCharges (Output.paidStore (before ctx host) (paid ctx host)) "k".toUTF8.toList)

def flag (ctx : Context) (host : NearState) : UInt64 :=
  if ((paid ctx host).storage "k".toUTF8.toList).isSome then 1 else 0

/-- The computed arbitrary canonical write preserves every resource outside
storage, trie accounting, billing and synchronized runtime counters. -/
theorem after_frame (ctx : Context) (host : NearState) :
    StorageFrame.Frame (before ctx host) (after ctx host) := by
  simpa only [after, phase, StorageCanonical.LookupPlan.result, paid] using
    StorageFrame.composed_frame ctx.protocol.fees.numExtraBytesRecord (before ctx host)
      (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0) _ _
      1 0 u64Max 0 "k".toUTF8.toList ctx.args

private theorem key_read (ctx : Context) (raw : Storage) (b : HostStore NearState)
    (hm : b.mem = preparedData ctx.protocol) (hp : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg b 0 1 = some "k".toUTF8.toList := by
  let ref := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  have he : b.mem = ref.mem := hm.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw).symm
  calc
    getMemOrReg b 0 1 = getMemOrReg ref 0 1 := by
      simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte, he]
    _ = _ := emptyPaid_key ctx raw hp

/-- Before/after resources are derived from the original functional host. -/
theorem paid_resources (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    PreEq (origin ctx raw) (paid ctx host) ∧
      (paid ctx host).registers 0 = some ctx.args := by
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hp := hb.1.fields.trans (PreEq.charges (before ctx host).host (preCharges ctx host)
    (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0))
  have hr := congrArg (fun ns : NearState => ns.registers 0)
    (applyCharges_frame (before ctx host).host (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0))
  exact ⟨by simpa only [paid] using hp, by simpa only [paid] using hr.trans hb.2⟩

/-- Complete actual canonical storage call, with computed gas/post-state and
old-value flag. The original proof observer is evaluated on actual fetched state. -/
theorem invoke (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hnodes : ctx.trie.NonzeroNodes) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hc : (before ctx host).host.gas.Credits (cost ctx host + rest))
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    (metered ctx.protocol.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
      (before ctx host) (args 1 0 u64Max 0) = .Return [.i64 (flag ctx host)] (after ctx host) ∧
    (after ctx host).host.gas.burnt = (before ctx host).host.gas.burnt + cost ctx host ∧
    (after ctx host).host.gas.Credits rest ∧
    (after ctx host).host.context.storageUsage = UInt64.ofNat
      (writeUsage ctx.protocol.fees.numExtraBytesRecord (phase ctx host) "k".toUTF8.toList ctx.args) ∧
    (after ctx host).host.gas.promises = (before ctx host).host.gas.promises := by
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hpf := (paid_resources ctx raw host hh).1
  have hr := (paid_resources ctx raw host hh).2
  have hrep : StorageOverlay.Represents (paid ctx host) ctx raw := by
    refine ⟨hpf.current, ?_⟩
    intro key
    rw [hpf.storage]
    rfl
  have hk := key_read ctx raw (Output.paidStore (before ctx host) (paid ctx host)) hb.1.memory hpages
  have hv : getMemOrReg (Output.paidStore (before ctx host) (paid ctx host)) 0 u64Max = some ctx.args := by
    simpa only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero, Output.paidStore] using hr
  have hkl : withinLimit (paid ctx host).config.maxStorageKeyLen "k".toUTF8.toList.length = true := by
    rw [hpf.config, show "k".toUTF8.toList.length = 1 by decide +kernel]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageKey) 1 = true
    simpa [withinLimit] using hkey
  have hvl : withinLimit (paid ctx host).config.maxStorageValueLen ctx.args.length = true := by
    rw [hpf.config]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageValue) ctx.args.length = true
    simpa [withinLimit] using hvalue
  have hcurrent : (paid ctx host).context.currentAccountId = ctx.current.bytes := hpf.current
  have hp : recordedStorageError (paid ctx host)
      ((lookup ctx host).fetched.set
        (Near.TrieOverlay.contractKey (paid ctx host).context.currentAccountId "k".toUTF8.toList) ctx.args) = none := by
    simpa only [lookup, recordedStorageError, hcurrent, hpf.config, hpf.proof] using hproof
  have hm := StorageCanonical.metered_canonical_credits ctx.protocol.fees.numExtraBytesRecord
    (before ctx host) (paid ctx host) ctx raw.toFinset hwf raw rfl hrep hnodes
    1 0 u64Max 0 "k".toUTF8.toList ctx.args rest hb.1.isView (by unfold paid; rfl)
    hpf.accounting hk hv hkl hvl (by simpa only [cost, lookup, preCharges, FundedEmpty.preCharges, before, Nat.add_assoc] using hc) hp
  have hext : (paid ctx host).extCosts = (before ctx host).host.extCosts := by
    have hf := congrArg NearState.extCosts
      (applyCharges_frame (before ctx host).host (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0))
    simpa only [paid] using hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [after, phase, lookup, flag] using hm.1
  · simpa only [after, phase, cost, lookup, preCharges, FundedEmpty.preCharges, before, hext, Nat.add_assoc] using hm.2.1
  · simpa only [after, phase, lookup] using hm.2.2.1
  · simpa only [after, phase, lookup] using hm.2.2.2.1
  · simpa only [after, phase, lookup] using hm.2.2.2.2

/-- Initial body credits discharge the actual storage frontier for either
fresh or replacement keys on any canonical WF trie. -/
theorem frontier (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hnodes : ctx.trie.NonzeroNodes) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hc : host.gas.Credits (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest))
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    StorageFrontier ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest (flag ctx host) := by
  have hs := StorageCredits.body_storage ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest
    (by simpa only [bodyStore, FundedEmpty.bodyStore, initialized_host] using hc)
  have hm := invoke ctx raw host _ hh hwf hnodes hpages hkey hvalue
    (by simpa only [before, FundedEmpty.before] using hs) hproof
  refine ⟨?_, ?_, ?_, hm.2.2.1⟩
  · simpa only [before, FundedEmpty.before, args, inputBefore] using hm.1
  · exact Nat.le_of_eq (by simpa only [before, FundedEmpty.before, inputBefore] using hm.2.1)
  · change (after ctx host).host.gas.burnt + (after ctx host).host.gas.promises ≤ _
    rw [hm.2.1, hm.2.2.2.2]
    simp only [before, FundedEmpty.before, bodyStore, inputBefore, GasCounter.used]
    omega

/-- Every accepted instruction in the actual walking body, for an arbitrary
canonical original trie and either old-value branch. No storage callback remains. -/
theorem body_success (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat) (limits : ExecLimits)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hnodes : ctx.trie.NonzeroNodes)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hc : host.gas.Credits (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest))
    (hproof : recordedStorageError (origin ctx raw)
      ((StorageCanonical.plan ctx.trie (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
        (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    WP ctx.protocol.wasm 16 (.next (atCode (bodyStore ctx host) limits #[] saveFrame [] module.funcs[0]!.body))
      (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest)
      (fun remaining final error => remaining = rest ∧ final = .done []
        ((successResults ctx.protocol (bodyStore ctx host) (after ctx host)).finalStore ctx.protocol.wasm
          (bodyStore ctx host)) ∧ error = none) := by
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hf := after_frame ctx host
  have hcfg := hf.config.trans hb.1.fields.config
  have hlogs : (after ctx host).host.logs = [] := hf.logs.trans (congrArg NearState.logs hb.1.fields)
  have hext : (after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hinput : host.context.input = ctx.args := hh.input
  have hregister := (congrFun hf.registers 0).trans hb.2
  have hs := frontier ctx raw host rest hh hwf hnodes hpages hm.key hm.value hc hproof
  have hw := wp_save_success ctx.protocol host ctx.protocol.wasm.limits.initialMemoryPages
    (some ctx.protocol.wasm.limits.maxMemoryPages) (after ctx host) (cost ctx host) rest (flag ctx host) limits hpages
    (by rw [hh.config, hinput]
        change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
        simpa [withinLimit] using hm.input)
    (hf.1.trans hb.1.memory) (by rw [hinput]; exact hregister)
    (by rw [hcfg, hinput]
        change withinLimit (some ctx.protocol.wasm.limits.maxLengthReturnedData) ctx.args.length = true
        simpa [withinLimit] using hm.returned)
    (by simp only [logCountError, hcfg, hlogs]
        change (if 0 ≥ ctx.protocol.wasm.limits.maxNumberLogs then _ else none) = none
        simp only [Nat.not_le.mpr hm.logs, ↓reduceIte])
    (by simp only [logSpace, hcfg, totalLogLength, hlogs, List.map_nil, List.sum_nil]
        change 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength - 0
        simpa using hm.logBytes)
    (by rw [hext]; exact hread)
    (by intro limit hl
        have hl' := congrArg NearConfig.maxLogLen hcfg
        change (after ctx host).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength at hl'
        rw [hl'] at hl
        cases Option.some.inj hl
        simpa only [totalLogLength, hlogs, List.map_nil, List.sum_nil, Nat.zero_add] using hm.logBytes)
    (by simpa only [bodyStore, FundedEmpty.bodyStore, preparedData] using hc)
    (by simpa only [bodyStore, FundedEmpty.bodyStore, preparedData] using hs)
  simpa only [bodyStore, FundedEmpty.bodyStore, preparedData] using hw

/-- Canonical preparation preserves the storage and resources consumed by the
raw write; its explicit new trie/accounting state remains available in phase. -/
theorem phase_frame (ctx : Context) (host : NearState) :
    StorageFrame.Frame (before ctx host) (phase ctx host) := by
  simpa only [phase, StorageCanonical.LookupPlan.result, paid] using
    (StorageFrame.prepayment_frame (before ctx host) (preCharges ctx host)
      (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0)).trans (StorageFrame.prepared_frame _ _ _)

theorem phase_storage (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    (phase ctx host).host.storage = (origin ctx raw).storage := by
  simpa only [phase, StorageCanonical.LookupPlan.result, prepared, Output.paidStore] using
    (paid_resources ctx raw host hh).1.storage

theorem phase_usage (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) :
    (phase ctx host).host.context.storageUsage = UInt64.ofNat ctx.storageUsage := by
  have hf := congrArg (fun ns : NearState => ns.context.storageUsage) (paid_resources ctx raw host hh).1
  simpa only [phase, StorageCanonical.LookupPlan.result, prepared, Output.paidStore, preView,
    origin, VMContext.toNearState, Near.Boundary.toVMContext] using hf

theorem phase_represents (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset) :
    StorageRepresentation.Represents (phase ctx host).host raw.toFinset := by
  have hr := StorageRepresentation.toNearState_represents ctx.protocol (Near.Boundary.toVMContext ctx)
    raw raw.toFinset rfl hwf.raw_keys_unique
  change StorageRepresentation.Represents (origin ctx raw) raw.toFinset at hr
  have hs := phase_storage ctx raw host hh
  have hk : (phase ctx host).host.storageKeys = (origin ctx raw).storageKeys := by
    have hf := congrArg NearState.storageKeys (paid_resources ctx raw host hh).1
    simpa only [phase, StorageCanonical.LookupPlan.result, prepared, Output.paidStore, preView] using hf
  constructor
  · intro key value
    rw [hs]
    exact hr.lookup key value
  · intro key value hm
    rw [hk]
    exact hr.coverage key value hm

end WNear.Skeleton.CanonicalBody
