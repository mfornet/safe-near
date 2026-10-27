import Skeleton.FunctionalInvariant
import Skeleton.SuccessCost

/-! Auxiliary funded bodies keep the original guest context; only internal
gas limits are enlarged. All byte-cost width assumptions are explicit. -/
namespace WNear.Skeleton.FundedEmpty
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def bodyStore (ctx : Context) (host : NearState) :=
  initializedStore ctx.protocol host (preparedData ctx.protocol)
def before (ctx : Context) (host : NearState) :=
  inputBefore ctx.protocol.wasm (successStorageBefore ctx.protocol (bodyStore ctx host)) moduleInstance
def preCharges (ctx : Context) (host : NearState) :=
  chargesBefore "storage_write" (before ctx host) (args 1 0 u64Max 0)
@[irreducible] def paid (ctx : Context) (host : NearState) :=
  (applyCharges (before ctx host).host (preCharges ctx host)).1
def cost (ctx : Context) (host : NearState) := burnSum (before ctx host).host.extCosts (preCharges ctx host)
@[irreducible] def phase (ctx : Context) (host : NearState) : HostStore NearState :=
  let b := Output.paidStore (before ctx host) (paid ctx host)
  let p := (applyCharges (accounted b ctx.trie).host (trieCharges ctx.trie ctx.trie)).1
  prepared b p (ctx.trie.set (Near.TrieOverlay.contractKey (paid ctx host).context.currentAccountId
    "k".toUTF8.toList) ctx.args)
@[irreducible] def after (ctx : Context) (host : NearState) : HostStore NearState :=
  let b := phase ctx host
  let p := (applyCharges (written b "k".toUTF8.toList ctx.args).host
    (postCharges b "k".toUTF8.toList)).1
  finished ctx.protocol.fees.numExtraBytesRecord b 1 0 u64Max 0 "k".toUTF8.toList ctx.args p

private theorem chargedMany_preEq (store : Store NearState) (op count : Nat) :
    PreEq store.host (chargedMany store op count).host := by
  induction count generalizing store with
  | zero => rfl
  | succ n ih => exact (PreEq.charged store.host op).trans (ih (chargedStore store op))

private theorem inputAfter_preEq (cfg : WasmConfig) (store : Store NearState) :
    PreEq store.host (inputAfter cfg store moduleInstance 0).host := by
  have h := congrArg (fun st : HostStore NearState => preView st.host)
    (Input.paid_frame (inputBefore cfg store moduleInstance))
  simpa only [PreEq, inputAfter, NearState.setRegister, preView, inputBefore, chargedStore, chargeHost] using h

/-- The computed storage entry retains original resources for arbitrary billing. -/
theorem before_resources (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host) :
    BeforeWrite ctx raw (before ctx host) ∧ (before ctx host).host.registers 0 = some ctx.args := by
  have hc := chargedMany_preEq (bodyStore ctx host) ctx.protocol.wasm.regularOpCost 1
  have hi := inputAfter_preEq ctx.protocol.wasm (successInputBefore ctx.protocol (bodyStore ctx host))
  have hf := chargedMany_preEq
    (commitCall ctx.protocol.wasm (successInputBefore ctx.protocol (bodyStore ctx host))
      (successInputAfter ctx.protocol (bodyStore ctx host))) ctx.protocol.wasm.regularOpCost 5
  have hp : PreEq (origin ctx raw) (before ctx host).host :=
    hhost.trans (hc.trans (hi.trans (hf.trans (PreEq.charged _ _))))
  refine ⟨⟨hp, rfl⟩, ?_⟩
  have hr : (before ctx host).host.registers 0 = some host.context.input := by
    simp only [before, successStorageBefore, chargedMany, chargedStore, chargeHost, commitCall_host,
      successInputAfter, inputAfter, NearState.setRegister, UInt64.toNat_zero, ↓reduceIte,
      inputBefore, successInputBefore, bodyStore, initialized_host]
  rw [hr, hhost.input]
  rfl

private theorem key_read (ctx : Context) (raw : Storage) (b : HostStore NearState)
    (hm : b.mem = preparedData ctx.protocol) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg b 0 1 = some "k".toUTF8.toList := by
  let ref := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  have hmem : b.mem = ref.mem := hm.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw).symm
  calc
    getMemOrReg b 0 1 = getMemOrReg ref 0 1 := by
      simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte, hmem]
    _ = _ := emptyPaid_key ctx raw hpages

/-- The complete computed write frames arbitrary internal billing. -/
theorem after_frame (ctx : Context) (host : NearState) : StorageFrame.Frame (before ctx host) (after ctx host) := by
  simpa only [after, phase, paid] using StorageFrame.composed_frame ctx.protocol.fees.numExtraBytesRecord (before ctx host)
    (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0) _ _ 1 0 u64Max 0
    "k".toUTF8.toList ctx.args

attribute [irreducible] before bodyStore

/-- A local actual empty write from any framed initial body host. -/
theorem invoke (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hcredits : (before ctx host).host.gas.Credits (cost ctx host + rest))
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    (metered ctx.protocol.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
      (before ctx host) (args 1 0 u64Max 0) = .Return [.i64 0] (after ctx host) ∧
    (after ctx host).host.gas.burnt = (before ctx host).host.gas.burnt + cost ctx host ∧
    (after ctx host).host.gas.Credits rest ∧
    (after ctx host).host.gas.promises = (before ctx host).host.gas.promises := by
  have hb := before_resources ctx raw host hhost
  have hp := hb.1.paid (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0)
  have hpf : PreEq (origin ctx raw) (paid ctx host) := by
    simpa only [paid] using hb.1.fields.trans
      (PreEq.charges (before ctx host).host (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0))
  have hr := congrArg (fun st : NearState => st.registers 0)
    (applyCharges_frame (before ctx host).host (preCharges ctx host) (StorageBudget.plan_burnsOnly _ 1 0 u64Max 0))
  have hregister : (paid ctx host).registers 0 = some ctx.args := by
    simpa only [paid] using hr.trans hb.2
  have hrep : StorageOverlay.Represents (paid ctx host) ctx raw := by
    refine ⟨hpf.current, ?_⟩
    intro key
    rw [hpf.storage]
    rfl
  have hn := StorageEmpty.storage_none (Output.paidStore (before ctx host) (paid ctx host)) ctx raw.toFinset hwf raw rfl
    ⟨hrep.1, hrep.2⟩ "k".toUTF8.toList hentries hselected
  have hpost : postCharges (Output.paidStore (before ctx host) (paid ctx host)) "k".toUTF8.toList = [] := by
    simp only [postCharges, hn]
  have hkeyRead := key_read ctx raw _ (show (Output.paidStore (before ctx host) (paid ctx host)).mem = preparedData ctx.protocol from hb.1.memory) hpages
  have hvalueRead : getMemOrReg (Output.paidStore (before ctx host) (paid ctx host)) 0 u64Max = some ctx.args := by
    simpa only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero, Output.paidStore] using hregister
  have hkl : withinLimit (paid ctx host).config.maxStorageKeyLen "k".toUTF8.toList.length = true := by
    rw [hpf.config, show "k".toUTF8.toList.length = 1 by decide +kernel]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageKey) 1 = true
    simpa [withinLimit] using hkey
  have hvl : withinLimit (paid ctx host).config.maxStorageValueLen ctx.args.length = true := by
    rw [hpf.config]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageValue) ctx.args.length = true
    simpa [withinLimit] using hvalue
  have hpc : recordedStorageError (paid ctx host)
      (ctx.trie.set (Near.TrieOverlay.contractKey (paid ctx host).context.currentAccountId "k".toUTF8.toList) ctx.args) = none := by
    have hcurrent : (paid ctx host).context.currentAccountId = ctx.current.bytes := hpf.current
    simpa only [recordedStorageError, hcurrent, hpf.config, hpf.proof] using hproof
  have hm := StorageEmpty.metered_empty_sufficient ctx.protocol.fees.numExtraBytesRecord
    (before ctx host) (paid ctx host) ctx raw.toFinset hwf raw rfl ⟨hrep.1, hrep.2⟩
    1 0 u64Max 0 "k".toUTF8.toList ctx.args rest hb.1.isView (by unfold paid; rfl) hpf.isView hpf.accounting
    hkeyRead hvalueRead hkl hvl hentries hselected (by
      rw [StorageEmpty.trieCharges_self_cost, hpost]
      simpa only [cost, preCharges, burnSum, List.map_nil, List.sum_nil, Nat.zero_add] using hcredits) hpc
  have hn' : (paid ctx host).storage "k".toUTF8.toList = none := hn
  simp only [hn', Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    StorageEmpty.trieCharges_self_cost, hpost, Nat.add_zero] at hm
  simpa only [after, phase, cost, preCharges, burnSum, List.map_nil, List.sum_nil, Nat.add_zero] using
    And.intro hm.1 (And.intro hm.2.1 (And.intro hm.2.2.1 hm.2.2.2.2))


/-- Initial body credits derive the storage frontier at its actual call site. -/
theorem frontier (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hcredits : host.gas.Credits (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest))
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    StorageFrontier ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest 0 := by
  have hc := StorageCredits.body_storage ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest (by simpa only [bodyStore, initialized_host] using hcredits)
  have hm := invoke ctx raw host _ hhost hwf hpages hkey hvalue hentries hselected
    (by simpa only [before] using hc) hproof
  refine ⟨?_, ?_, ?_, hm.2.2.1⟩
  · simpa only [before, args, inputBefore] using hm.1
  · exact Nat.le_of_eq (by simpa only [before, inputBefore] using hm.2.1)
  · change (after ctx host).host.gas.burnt + (after ctx host).host.gas.promises ≤ _
    rw [hm.2.1, hm.2.2.2]
    simp only [before, inputBefore, GasCounter.used]
    omega

/-- Accepted VM resource checks give a concrete full body WP from any framed
initial host; storage is discharged rather than supplied as a callback. -/
theorem body_success (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat) (limits : ExecLimits)
    (hhost : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hcredits : host.gas.Credits (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest))
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    WP ctx.protocol.wasm 16 (.next (atCode (bodyStore ctx host) limits #[] saveFrame [] module.funcs[0]!.body))
      (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest)
      (fun remaining final error => remaining = rest ∧ final = .done []
        ((successResults ctx.protocol (bodyStore ctx host) (after ctx host)).finalStore ctx.protocol.wasm
          (bodyStore ctx host)) ∧ error = none) := by
  have hb := before_resources ctx raw host hhost
  have hf := after_frame ctx host
  have hcfg := hf.config.trans hb.1.fields.config
  have hlogs : (after ctx host).host.logs = [] := hf.logs.trans (congrArg NearState.logs hb.1.fields)
  have hext : (after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hinput : host.context.input = ctx.args := hhost.input
  have hregister := (congrFun hf.registers 0).trans hb.2
  have hs := frontier ctx raw host rest hhost hwf hpages hm.key hm.value hentries hselected hcredits hproof
  have hw := wp_save_success ctx.protocol host ctx.protocol.wasm.limits.initialMemoryPages
    (some ctx.protocol.wasm.limits.maxMemoryPages) (after ctx host) (cost ctx host) rest 0 limits hpages
    (by rw [hhost.config, hinput]
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
        have hh := congrArg NearConfig.maxLogLen hcfg
        change (after ctx host).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength at hh
        rw [hh] at hl
        cases Option.some.inj hl
        simpa only [totalLogLength, hlogs, List.map_nil, List.sum_nil, Nat.zero_add] using hm.logBytes)
    (by simpa only [bodyStore, preparedData] using hcredits)
    (by simpa only [bodyStore, preparedData] using hs)
  simpa only [bodyStore, preparedData] using hw


/-- Successful storage prebilling depends only on original protocol and input. -/
theorem cost_eq (ctx : Context) (raw : Storage) (host : NearState)
    (hhost : PreEq (origin ctx raw) host)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    cost ctx host = emptyStorageCost ctx.protocol ctx.args.length := by
  have hb := before_resources ctx raw host hhost
  have hk := key_read ctx raw (before ctx host) hb.1.memory hpages
  have hv : getMemOrReg (before ctx host) 0 u64Max = some ctx.args := by
    simpa only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero] using hb.2
  have hkl := congrArg NearConfig.maxStorageKeyLen hb.1.fields.config
  have hvl := congrArg NearConfig.maxStorageValueLen hb.1.fields.config
  have hkeyLimit : (before ctx host).host.config.maxStorageKeyLen = some ctx.protocol.wasm.limits.maxLengthStorageKey := hkl
  have hvalueLimit : (before ctx host).host.config.maxStorageValueLen = some ctx.protocol.wasm.limits.maxLengthStorageValue := hvl
  have ht : (before ctx host).host.storageAccounting = some ctx.trie := hb.1.fields.accounting
  have hext : (before ctx host).host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hb.1.fields
  have hbytes : "k".toUTF8.toList = [107] := by decide +kernel
  rw [hbytes] at hk
  have hp : storageMutationPlan? "storage_write" (before ctx host) (args 1 0 u64Max 0) =
      some { charges := [.ext "base", .ext "storage_write_base", .ext "read_memory_base", .ext "read_memory_byte" 1,
        .ext "read_register_base", .ext "read_register_byte" ctx.args.length,
        .ext "storage_write_key_byte" 1, .ext "storage_write_value_byte" ctx.args.length] } := by
    simp [storageMutationPlan?, args, argU64, hk, hv, hkeyLimit, hvalueLimit, Nat.not_lt.mpr hkey,
      Nat.not_lt.mpr hvalue, readSpan, hb.2, show (1 : UInt64) ≠ u64Max by decide +kernel, storageValueCharges, ht]
  simp only [cost, preCharges, chargesBefore, hp, hext]
  simp [burnSum, burnCost, emptyStorageCost, Nat.add_assoc]

/-- A uniform original-data body bound holds even when the internal gas
counter has been enlarged; guest-visible prepaid gas is retained. -/
theorem budget_le (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hhost : PreEq (origin ctx raw) host)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest ≤ saveEmptyCost ctx + rest := by
  have hb := before_resources ctx raw host hhost
  have hf := after_frame ctx host
  have hext : (after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hfees : (after ctx host).host.fees = ctx.protocol.fees.actionFees :=
    hf.fees.trans (congrArg NearState.fees hb.1.fields)
  have ho := congrArg NearState.outputDataReceivers hf.2
  have hreceivers : (after ctx host).host.outputDataReceivers = (Near.Boundary.toVMContext ctx).outputDataReceivers :=
    ho.trans (congrArg NearState.outputDataReceivers hb.1.fields)
  have hcurrent : (after ctx host).host.context.currentAccountId = ctx.current.bytes :=
    hf.currentAccountId.trans hb.1.fields.current
  have hregister := (congrFun hf.registers 0).trans hb.2
  have hr := successReturn_cost_le ctx.protocol (bodyStore ctx host) (after ctx host) ctx.args hregister
  rw [hext, hfees, hreceivers, hcurrent] at hr
  have hhostExt : host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hhost
  have hi : Input.cost (successInputBefore ctx.protocol (bodyStore ctx host)).host =
      ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "write_register_base" := by
    simp only [Input.cost, successInputBefore, chargedMany, chargedStore, chargeHost, bodyStore, initialized_host, hhostExt]
  have hl : (successLogBefore ctx.protocol (bodyStore ctx host) (after ctx host)).host.extCosts = ctx.protocol.wasm.extCosts := hext
  unfold successBudget
  rw [hi, cost_eq ctx raw host hhost hpages hkey hvalue, hl]
  unfold saveEmptyCost
  dsimp only
  omega

/-- A genuinely funded auxiliary body. Only the internal counter limits are
enlarged; no premise assumes that original gasLimit covers the cost. -/
theorem funded_body_success (ctx : Context) (raw : Storage) (rest : Nat) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := enlargeHost (origin ctx raw) (saveEmptyCost ctx + rest)
    WP ctx.protocol.wasm 16 (.next (atCode (bodyStore ctx host) limits #[] saveFrame [] module.funcs[0]!.body))
      (successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest)
      (fun remaining final error => remaining = rest ∧ final = .done []
        ((successResults ctx.protocol (bodyStore ctx host) (after ctx host)).finalStore ctx.protocol.wasm
          (bodyStore ctx host)) ∧ error = none) := by
  let host := enlargeHost (origin ctx raw) (saveEmptyCost ctx + rest)
  have hf : PreEq (origin ctx raw) host := PreEq.enlarged _ _
  have hc : host.gas.Credits (saveEmptyCost ctx + rest) :=
    enlarged_initial_credits ctx.protocol (Near.Boundary.toVMContext ctx) raw (saveEmptyCost ctx + rest)
  exact body_success ctx raw host rest limits hf hwf hpages hm hread hentries hselected
    (hc.mono (budget_le ctx raw host rest hf hpages hm.key hm.value)) hproof


/-- The actual sixteen-step auxiliary high run reaches its computed successful
body state, with original guest-visible context and no execution callback. -/
theorem funded_body_run (ctx : Context) (raw : Storage) (rest : Nat) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let host := enlargeHost (origin ctx raw) (saveEmptyCost ctx + rest)
    runMetered ctx.protocol.wasm 16 (phaseMachine (bodyStore ctx host) limits 0 0) =
      (.done [] ((successResults ctx.protocol (bodyStore ctx host) (after ctx host)).finalStore
        ctx.protocol.wasm (bodyStore ctx host)), none) := by
  have hw := funded_body_success ctx raw rest limits hwf hpages hm hread hentries hselected hproof
  obtain ⟨_, hp, _⟩ := hw.result
  exact Prod.ext hp.2.1 hp.2.2

end WNear.Skeleton.FundedEmpty
