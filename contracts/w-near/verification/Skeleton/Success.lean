import Skeleton.Calls

/-!
# The whole body with storage as its sole host frontier

Input and the two output calls are instantiated by their proved contracts.
The remaining semantic frontier is one local storage-write invocation and its
gas accounting. Resource premises describe the input and the storage post-state.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

set_option maxHeartbeats 300000
set_option maxRecDepth 10000

def successInputBefore (cfg : RuntimeConfig) (store : Store NearState) :=
  chargedMany store cfg.wasm.regularOpCost 1

def successInputAfter (cfg : RuntimeConfig) (store : Store NearState) :=
  inputAfter cfg.wasm (successInputBefore cfg store) moduleInstance 0

def successStorageBefore (cfg : RuntimeConfig) (store : Store NearState) :=
  chargedMany (commitCall cfg.wasm (successInputBefore cfg store) (successInputAfter cfg store))
    cfg.wasm.regularOpCost 5

def successLogBefore (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState) :=
  chargedMany (chargedStore (commitCall cfg.wasm (successStorageBefore cfg store) storage)
    cfg.wasm.regularOpCost) cfg.wasm.regularOpCost 2

@[irreducible] def successLogAfter (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState) :=
  savedAfter (inputBefore cfg.wasm (successLogBefore cfg store storage) moduleInstance)

def successReturnBefore (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState) :=
  chargedMany (commitCall cfg.wasm (successLogBefore cfg store storage)
    (successLogAfter cfg store storage)) cfg.wasm.regularOpCost 2

/-- All host results except storage are deterministic operations supplied by
existing proved contracts, without running the method or any instruction suffix. -/
@[irreducible] def successResults (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState) :
    HostResults :=
  { input := successInputAfter cfg store, storage,
    log := successLogAfter cfg store storage,
    returned := returnedAfter cfg.wasm (successReturnBefore cfg store storage) store.host.context.input }

@[simp] theorem successResults_input (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).input =
      successInputAfter cfg store := by simp only [successResults]

@[simp] theorem successResults_storage (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).storage = storage := by
  simp only [successResults]

@[simp] theorem successResults_log (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).log =
      successLogAfter cfg store storage := by simp only [successResults]

@[simp] theorem successResults_returned (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).returned =
      returnedAfter cfg.wasm (successReturnBefore cfg store storage) store.host.context.input := by
  simp only [successResults]

@[simp] theorem successResults_beforeInput (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).beforeInput cfg.wasm store =
      successInputBefore cfg store := rfl

@[simp] theorem successResults_beforeStorage (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).beforeStorage cfg.wasm store =
      successStorageBefore cfg store := by
  simp only [HostResults.beforeStorage, HostResults.afterInput, successResults_input,
    successResults_beforeInput, successStorageBefore]

@[simp] theorem successResults_beforeLog (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).beforeLog cfg.wasm store =
      successLogBefore cfg store storage := by
  simp only [HostResults.beforeLog, HostResults.afterDrop, HostResults.afterStorage,
    successResults_beforeStorage, successResults_storage, successLogBefore]

@[simp] theorem successResults_beforeReturn (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) : (successResults cfg store storage).beforeReturn cfg.wasm store =
      successReturnBefore cfg store storage := by
  simp only [HostResults.beforeReturn, HostResults.afterLog, successResults_beforeLog,
    successResults_log, successReturnBefore]

/-- Costs are computed from semantic charge plans, with only the storage bound
supplied externally. In particular the return cost includes output receivers. -/
@[irreducible] def successCosts (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState)
    (storageCost : Nat) : HostCosts :=
  { input := MeteredHosts.Input.cost (successInputBefore cfg store).host,
    storage := storageCost,
    log := MeteredHosts.burnSum (successLogBefore cfg store storage).host.extCosts savedCharges,
    returned := returnCost cfg.wasm (successReturnBefore cfg store storage) }

@[simp] theorem successCosts_input (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (storageCost : Nat) :
    (successCosts cfg store storage storageCost).input =
      MeteredHosts.Input.cost (successInputBefore cfg store).host := by unfold successCosts; rfl

@[simp] theorem successCosts_storage (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (storageCost : Nat) :
    (successCosts cfg store storage storageCost).storage = storageCost := by unfold successCosts; rfl

@[simp] theorem successCosts_log (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (storageCost : Nat) :
    (successCosts cfg store storage storageCost).log =
      MeteredHosts.burnSum (successLogBefore cfg store storage).host.extCosts savedCharges := by
  unfold successCosts; rfl

@[simp] theorem successCosts_returned (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (storageCost : Nat) :
    (successCosts cfg store storage storageCost).returned =
      returnCost cfg.wasm (successReturnBefore cfg store storage) := by unfold successCosts; rfl

/-- The explicit body budget, excluding loading and entry activation. -/
def successBudget (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState)
    (storageCost rest : Nat) :=
  15 * cfg.wasm.regularOpCost + MeteredHosts.Input.cost (successInputBefore cfg store).host +
    storageCost + MeteredHosts.burnSum (successLogBefore cfg store storage).host.extCosts savedCharges +
    returnCost cfg.wasm (successReturnBefore cfg store storage) + rest

theorem successBudget_eq (cfg : RuntimeConfig) (store : Store NearState) (storage : HostStore NearState)
    (storageCost rest : Nat) :
    (successCosts cfg store storage storageCost).bodyBudget cfg.wasm.regularOpCost rest =
      successBudget cfg store storage storageCost rest := by
  rw [HostCosts.bodyBudget_eq]
  simp only [successCosts_input, successCosts_storage, successCosts_log, successCosts_returned, successBudget]

private theorem charged_credits (store : Store NearState) (cost rest : Nat)
    (h : store.host.gas.Credits (cost + rest)) :
    (chargedStore store cost).host.gas.Credits rest :=
  (Pays.chargeWasm (.done [] store) cost rest h).2.2.2.2

private theorem chargedMany_credits (store : Store NearState) (cost rest n : Nat)
    (h : store.host.gas.Credits (n * cost + rest)) :
    (chargedMany store cost n).host.gas.Credits rest := by
  induction n generalizing store with
  | zero => simpa [chargedMany] using h
  | succ n ih =>
    apply ih
    apply charged_credits
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem saved_register (st : HostStore NearState) (register : Nat) :
    (savedAfter st).host.registers register = st.host.registers register := by
  have h := MeteredHosts.applyCharges_frame st.host savedCharges (by
    simp only [savedCharges, extCharges, List.mem_map]
    rintro _ ⟨_, _, rfl⟩
    trivial)
  have hr := congrArg (fun ns : NearState => ns.registers register) h
  simpa only [savedAfter, MeteredHosts.Output.paidStore] using hr

private theorem saved_config (st : HostStore NearState) :
    (savedAfter st).host.config = st.host.config := by
  have h := MeteredHosts.applyCharges_frame st.host savedCharges (by
    simp only [savedCharges, extCharges, List.mem_map]
    rintro _ ⟨_, _, rfl⟩
    trivial)
  have hr := congrArg NearState.config h
  simpa only [savedAfter, MeteredHosts.Output.paidStore] using hr

/-- The storage call's remaining local semantic and gas obligations. -/
structure StorageFrontier (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64) : Prop where
  invoke : (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
    ⟨((successStorageBefore cfg store).memOf moduleInstance).getD (Memory.new 0 none),
      (chargedStore (successStorageBefore cfg store) cfg.wasm.regularOpCost).host⟩
    [.i64 1, .i64 0, .i64 u64Max, .i64 0, .i64 u64Max] = .Return [.i64 written] storage
  burnt : storage.host.gas.burnt ≤
    (chargedStore (successStorageBefore cfg store) cfg.wasm.regularOpCost).host.gas.burnt + storageCost
  used : storage.host.gas.used ≤
    (chargedStore (successStorageBefore cfg store) cfg.wasm.regularOpCost).host.gas.used + storageCost
  credits : storage.host.gas.Credits
    ((successCosts cfg store storage storageCost).storageSuffix cfg.wasm.regularOpCost rest)

/-- Package the one storage frontier without inspecting any method execution. -/
theorem storage_evidence (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64)
    (hmodule : (successStorageBefore cfg store).modules[0]? = some moduleInstance)
    (hfn : (successStorageBefore cfg store).funcs[1]? = some
      (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn))
    (hstorage : StorageFrontier cfg store storage storageCost rest written) :
    CallEvidence cfg.wasm (successStorageBefore cfg store) 1
      [.i64 1, .i64 0, .i64 u64Max, .i64 0, .i64 u64Max] [.i64 written]
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) storage
      (successCosts cfg store storage storageCost).storage
      ((successCosts cfg store storage storageCost).storageSuffix cfg.wasm.regularOpCost rest) := by
  refine ⟨hmodule, rfl, hfn, rfl, hstorage.invoke, ?_, ?_, hstorage.credits⟩
  · simpa only [successCosts_storage] using hstorage.burnt
  · simpa only [successCosts_storage] using hstorage.used

/-- Storage commits its supplied memory; the following three pure opcodes
preserve it. This equation also retains the initialized single-memory shape. -/
theorem successLog_memory (cfg : RuntimeConfig) (host : NearState) (memory : Memory)
    (storage : HostStore NearState) :
    (successLogBefore cfg (initializedStore cfg host memory) storage).memOf moduleInstance =
      some storage.mem := by rfl

private theorem chargedStore_config (store : Store NearState) (cost : Nat) :
    (chargedStore store cost).host.config = store.host.config := rfl

private theorem chargedStore_register (store : Store NearState) (cost register : Nat) :
    (chargedStore store cost).host.registers register = store.host.registers register := rfl

private theorem chargedMany_config (store : Store NearState) (cost n : Nat) :
    (chargedMany store cost n).host.config = store.host.config := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => rw [chargedMany, ih, chargedStore_config]

private theorem chargedMany_register (store : Store NearState) (cost n register : Nat) :
    (chargedMany store cost n).host.registers register = store.host.registers register := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => rw [chargedMany, ih, chargedStore_register]

private theorem inputBefore_config (cfg : WasmConfig) (store : Store NearState) :
    (inputBefore cfg store moduleInstance).host.config = store.host.config := rfl

private theorem inputBefore_register (cfg : WasmConfig) (store : Store NearState) (register : Nat) :
    (inputBefore cfg store moduleInstance).host.registers register = store.host.registers register := rfl

theorem successReturn_register (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (register : Nat) :
    (successReturnBefore cfg store storage).host.registers register = storage.host.registers register := by
  simp only [successReturnBefore, chargedMany_register, commitCall_host, successLogAfter,
    saved_register, inputBefore_register, successLogBefore, chargedStore_register]

theorem successReturn_config (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) :
    (successReturnBefore cfg store storage).host.config = storage.host.config := by
  simp only [successReturnBefore, chargedMany_config, commitCall_host, successLogAfter,
    saved_config, inputBefore_config, successLogBefore, chargedStore_config]

/-- The full actual body has only one remaining local host frontier: storage.
All resources are stated on the initial host or the storage post-state. -/
theorem wp_save_success (cfg : RuntimeConfig) (host : NearState) (pages : Nat) (max : Option Nat)
    (storage : HostStore NearState) (storageCost rest : Nat) (written : UInt64) (limits : ExecLimits)
    (hpages : 0 < pages)
    (hinputLimit : withinLimit host.config.maxRegisterLen host.context.input.length = true)
    (hmemory : storage.mem = dataMemory pages max)
    (hregister : storage.host.registers 0 = some host.context.input)
    (hreturnLimit : withinLimit storage.host.config.maxReturnLen host.context.input.length = true)
    (hcount : logCountError storage = none)
    (hspace : 5 ≤ logSpace storage)
    (hreadCost : storage.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, storage.host.config.maxLogLen = some limit → totalLogLength storage + 5 ≤ limit)
    (hcredits : host.gas.Credits
      (successBudget cfg (initializedStore cfg host (dataMemory pages max)) storage storageCost rest))
    (hstorage : StorageFrontier cfg (initializedStore cfg host (dataMemory pages max))
      storage storageCost rest written) :
    WP cfg.wasm 16
      (.next (atCode (initializedStore cfg host (dataMemory pages max)) limits #[]
        saveFrame [] module.funcs[0]!.body))
      (successBudget cfg (initializedStore cfg host (dataMemory pages max)) storage storageCost rest)
      (fun remaining final error => remaining = rest ∧ final = .done []
        ((successResults cfg (initializedStore cfg host (dataMemory pages max)) storage).finalStore
          cfg.wasm (initializedStore cfg host (dataMemory pages max))) ∧ error = none) := by
  let store := initializedStore cfg host (dataMemory pages max)
  let result := successResults cfg store storage
  let cost := successCosts cfg store storage storageCost
  have hhost : store.host = host := rfl
  have hc : store.host.gas.Credits (cost.bodyBudget cfg.wasm.regularOpCost rest) := by
    rw [successBudget_eq]
    exact hcredits
  have hlookup (stage : Store NearState) (hstage : stage ∈ bodyStages result cfg.wasm store) :=
    body_initialized_lookups cfg host (dataMemory pages max) result stage hstage
  have hinputLookup := hlookup (result.beforeInput cfg.wasm store) (by simp [bodyStages])
  have hstorageLookup := hlookup (result.beforeStorage cfg.wasm store) (by simp [bodyStages])
  have hlogLookup := hlookup (result.beforeLog cfg.wasm store) (by simp [bodyStages])
  have hreturnLookup := hlookup (result.beforeReturn cfg.wasm store) (by simp [bodyStages])
  simp only [result, successResults_beforeInput] at hinputLookup
  simp only [result, successResults_beforeStorage] at hstorageLookup
  simp only [result, successResults_beforeLog] at hlogLookup
  simp only [result, successResults_beforeReturn] at hreturnLookup
  have hic : (successInputBefore cfg store).host.gas.Credits
      (cost.inputBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    simpa [HostCosts.bodyBudget] using hc
  have hi := input_evidence cfg (successInputBefore cfg store)
    (cost.inputSuffix cfg.wasm.regularOpCost rest) hinputLookup.1 hinputLookup.2.1 hinputLimit
    (by simpa only [HostCosts.inputBudget, cost, successCosts_input, successInputAfter] using hic)
  have hs := storage_evidence cfg store storage storageCost rest written
    hstorageLookup.1 hstorageLookup.2.2.1 hstorage
  have hlc : (successLogBefore cfg store storage).host.gas.Credits
      (cost.logBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    apply charged_credits
    simpa [HostCosts.storageSuffix] using hstorage.credits
  have hl := log_evidence cfg (successLogBefore cfg store storage) pages max
    (cost.logSuffix cfg.wasm.regularOpCost rest) hlogLookup.1 hlogLookup.2.2.2.1 hpages
    (by rw [successLog_memory]; exact congrArg some hmemory) hcount hspace hreadCost hpush
    (by simpa only [HostCosts.logBudget, cost, successCosts_log] using hlc)
  have hrc : (successReturnBefore cfg store storage).host.gas.Credits
      (cost.returnBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    simpa [HostCosts.logSuffix, HostResults.afterLog, result, successResults,
      successLogAfter, cost, successCosts_log] using hl.credits
  have hr := return_evidence cfg (successReturnBefore cfg store storage) host.context.input rest
    hreturnLookup.1 hreturnLookup.2.2.2.2
    (by rw [successReturn_register]; exact hregister)
    (by rw [successReturn_config]; exact hreturnLimit)
    (by simpa only [HostCosts.returnBudget, cost, successCosts_returned, hhost] using hrc)
  have hbody : WP cfg.wasm 16 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (cost.bodyBudget cfg.wasm.regularOpCost rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (result.finalStore cfg.wasm store) ∧ error = none) := by
    apply wp_save_body cfg rest store limits cost result written hc
    · simpa only [result, successResults_beforeInput, successResults_input, cost, successCosts_input, successInputAfter] using hi
    · simpa only [result, successResults_beforeStorage, successResults_storage] using hs
    · simpa only [result, successResults_beforeLog, successResults_log, successLogAfter, cost, successCosts_log] using hl
    · simpa only [result, successResults_beforeReturn, successResults_returned, cost, successCosts_returned, hhost] using hr
  simpa only [cost, successBudget_eq, store, result] using hbody

end WNear.Skeleton
