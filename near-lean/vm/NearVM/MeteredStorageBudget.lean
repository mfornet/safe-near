import NearVM.MeteredHostBudget
import NearVM.MeteredHosts.StorageMeteredBudget

/-!
# Actual metered storage-call machine budget replay

Readiness is stated at the exact low host view after the Wasm call opcode
and the storage wrapper's actual precharges. The theorem resolves the real
module/function lookup, preserves caller stacks, commits host memory and
accounts for the final activation charge. Guest context remains functional
state; internal gas limits alone may vary.
-/
namespace Wasm.Near.MeteredStorageBudget
open MeteredLogic MeteredPrefix MeteredPureBudget MeteredHosts MeteredHostBudget
open MeteredHosts.StorageMetered

/-- The low state on which the real storage wrapper validates arguments. -/
def prechargedHost (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (keyLen keyPtr valueLen valuePtr : UInt64) : HostStore NearState :=
  StorageMeteredBudget.paid (hostView (chargedStore store cfg.regularOpCost) mi)
    keyLen keyPtr valueLen valuePtr

private theorem charge_logs (m : Machine) (cost : Nat) :
    (chargeWasm m cost).1.host.logs = m.host.logs := by cases m <;> rfl

private theorem call_logs (st : Store NearState) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (result : HostResult NearState) :
    (callResult st mi limits base frame callers code result).host.logs = (Budget.resultStore result).host.logs := by
  cases result <;> simp only [callResult, StepResult.host, atCode, commitHost_host, Budget.resultStore]

private theorem charge_error (host : NearState) (cost : Nat) {error : HostError}
    (he : (chargeHost host cost).2 = some error) : GasError error :=
  (GasCounter.deduct_error_is_gas host.gas cost cost he).elim Or.inr Or.inl

private theorem chargeWasm_error (m : Machine) (cost : Nat) {error : HostError}
    (he : (chargeWasm m cost).2 = some error) : GasError error := by
  cases m <;> exact charge_error _ cost he

private theorem charge_trap (st : Store NearState) (reason : Trap) (error : HostError)
    (hgas : GasError error) (hcause : trapError reason st.host = .hostError error) :
    GasFailure ((chargeWasm (.trap reason st) 0).1,
      (chargeWasm (.trap reason st) 0).2.map FunctionCallError.hostError) := by
  cases he : (chargeWasm (.trap reason st) 0).2 with
  | some error => exact ⟨error, chargeWasm_error _ _ he, Or.inl rfl⟩
  | none => exact ⟨error, hgas, Or.inr ⟨rfl, reason, chargedStore st 0, rfl, hcause⟩⟩

/-- The actual storage-call transition retains logs on all exits. No trie
readiness or accounting-success assumption is needed for this frame fact. -/
theorem advance_logs (cfg : WasmConfig) (extra : Nat) (store : Store NearState)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index addr : Nat)
    (keyLen keyPtr valueLen valuePtr : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (metered extra "storage_write" storageWriteFn).toHostFn))
    (hview : store.host.context.isView = false) :
    (advance cfg (.next (atCode store limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
      frame callers (.call index :: code)))).1.host.logs = store.host.logs := by
  rw [advance_host cfg store mi limits base (args keyLen keyPtr valueLen valuePtr) frame callers code index addr
    (metered extra "storage_write" storageWriteFn) hmodule haddr hfn rfl]
  cases he : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => rfl
  | none =>
    rw [charge_logs, call_logs]
    exact StorageMeteredBudget.metered_logs extra
      (hostView (chargedStore store cfg.regularOpCost) mi) keyLen keyPtr valueLen valuePtr hview

/-- The complete actual direct storage call satisfies local machine budget
simulation. Primitive readiness refers only to the low paid functional state;
there is no host-implementation replay callback or whole-run hypothesis. -/
theorem replay (cfg : WasmConfig) (extra : Nat) {small large : Store NearState}
    (h : StoreBelow small large) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (keyLen keyPtr valueLen valuePtr : UInt64)
    (hmodule : small.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : small.funcs[addr]? = some (.host (metered extra "storage_write" storageWriteFn).toHostFn))
    (hview : small.host.context.isView = false)
    (hready : preInvokeError "storage_write" (prechargedHost cfg small mi keyLen keyPtr valueLen valuePtr)
      (args keyLen keyPtr valueLen valuePtr) = none →
      StorageMeteredBudget.Ready (prechargedHost cfg small mi keyLen keyPtr valueLen valuePtr)
        keyLen keyPtr valueLen valuePtr)
    (hissue : small.host.lastExecutionIssue = none) :
    MatchesOrGas MachineBelow
      (advance cfg (.next (atCode small limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
        frame callers (.call index :: code))))
      (advance cfg (.next (atCode large limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
        frame callers (.call index :: code)))) := by
  have hmodules : small.modules = large.modules := by
    have hf := congrArg (fun store : Store NearState => store.modules) h.fields
    exact hf
  have hfuncs : small.funcs = large.funcs := by
    have hf := congrArg (fun store : Store NearState => store.funcs) h.fields
    exact hf
  have hmoduleLarge : large.modules[frame.inst]? = some mi := by rw [← hmodules]; exact hmodule
  have hfnLarge : large.funcs[addr]? = some (.host (metered extra "storage_write" storageWriteFn).toHostFn) := by
    rw [← hfuncs]; exact hfn
  have hviewLarge : large.host.context.isView = false :=
    (congrArg (·.isView) h.host.context).symm.trans hview
  have hs := advance_host cfg small mi limits base (args keyLen keyPtr valueLen valuePtr) frame callers code index addr
    (metered extra "storage_write" storageWriteFn) hmodule haddr hfn rfl
  have hl := advance_host cfg large mi limits base (args keyLen keyPtr valueLen valuePtr) frame callers code index addr
    (metered extra "storage_write" storageWriteFn) hmoduleLarge haddr hfnLarge rfl
  have hlogs : LogPrefix
      (advance cfg (.next (atCode small limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
        frame callers (.call index :: code)))).1
      (advance cfg (.next (atCode large limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
        frame callers (.call index :: code)))).1 := by
    refine ⟨[], ?_⟩
    simpa only [List.append_nil,
      advance_logs cfg extra small mi limits base frame callers code index addr keyLen keyPtr valueLen valuePtr
        hmodule haddr hfn hview,
      advance_logs cfg extra large mi limits base frame callers code index addr keyLen keyPtr valueLen valuePtr
        hmoduleLarge haddr hfnLarge hviewLarge] using h.host.logs
  cases hop : (chargeHost small.host cfg.regularOpCost).2 with
  | some error =>
    right
    refine ⟨⟨error, charge_error small.host _ hop, Or.inl ?_⟩, hlogs⟩
    simp only [hs, hop]
  | none =>
    have hc := chargedStore_below h cfg.regularOpCost hop
    have hv := hostView_below hc.2 mi
    rcases StorageMeteredBudget.replay extra hv keyLen keyPtr valueLen valuePtr hview hready hissue with
      hresult | ⟨error, after, hgas, hinvoke, hfresh, _⟩
    · have hstep := callResult_below hc.2 mi limits base frame callers code hresult
      cases hf : (chargeWasm (callResult (chargedStore small cfg.regularOpCost) mi limits base frame callers code
          ((metered extra "storage_write" storageWriteFn).invoke
            (hostView (chargedStore small cfg.regularOpCost) mi) (args keyLen keyPtr valueLen valuePtr))) 0).2 with
      | some error =>
        right
        refine ⟨⟨error, chargeWasm_error _ _ hf, Or.inl ?_⟩, hlogs⟩
        simp only [hs, hop, hf, Option.map_some]
      | none =>
        have hframe := chargeWasm_below hstep 0 hf
        left
        constructor
        · simpa only [hs, hl, hop, hc.1] using hframe.2.related
        · simp only [hs, hl, hop, hc.1, hf, hframe.1, Option.map_none]
    · right
      refine ⟨?_, hlogs⟩
      simp only [hs, hop, hinvoke, trapWith, callResult]
      apply charge_trap _ _ error (hgas.elim Or.inr Or.inl)
      rw [commitHost_host]
      simp only [trapError, hfresh]

/-- Replay of the actual uncharged `Exec.step` direct call. This isolates
host budget replay and host-memory commit before the metered runner surrounds
it with opcode and activation charges. -/
theorem step_replay (extra : Nat) {small large : Store NearState}
    (h : StoreBelow small large) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (keyLen keyPtr valueLen valuePtr : UInt64)
    (hmodule : small.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : small.funcs[addr]? = some (.host (metered extra "storage_write" storageWriteFn).toHostFn))
    (hview : small.host.context.isView = false)
    (hready : preInvokeError "storage_write"
      (StorageMeteredBudget.paid (hostView small mi) keyLen keyPtr valueLen valuePtr)
      (args keyLen keyPtr valueLen valuePtr) = none →
      StorageMeteredBudget.Ready
        (StorageMeteredBudget.paid (hostView small mi) keyLen keyPtr valueLen valuePtr)
        keyLen keyPtr valueLen valuePtr)
    (hissue : small.host.lastExecutionIssue = none) :
    MatchesOrGas MachineBelow
      (Exec.step (atCode small limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
        frame callers (.call index :: code)), none)
      (Exec.step (atCode large limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
        frame callers (.call index :: code)), none) := by
  have hmodules : small.modules = large.modules := by
    have hf := congrArg (fun store : Store NearState => store.modules) h.fields
    exact hf
  have hfuncs : small.funcs = large.funcs := by
    have hf := congrArg (fun store : Store NearState => store.funcs) h.fields
    exact hf
  have hmoduleLarge : large.modules[frame.inst]? = some mi := by rw [← hmodules]; exact hmodule
  have hfnLarge : large.funcs[addr]? = some (.host (metered extra "storage_write" storageWriteFn).toHostFn) := by
    rw [← hfuncs]; exact hfn
  rw [step_call small mi limits base (args keyLen keyPtr valueLen valuePtr) frame callers code index addr
      (metered extra "storage_write" storageWriteFn) hmodule haddr hfn rfl,
    step_call large mi limits base (args keyLen keyPtr valueLen valuePtr) frame callers code index addr
      (metered extra "storage_write" storageWriteFn) hmoduleLarge haddr hfnLarge rfl]
  rcases StorageMeteredBudget.replay extra (hostView_below h mi) keyLen keyPtr valueLen valuePtr hview hready hissue with
    hr | ⟨error, after, hgas, hinvoke, hfresh, hlogs⟩
  · exact Or.inl ⟨(callResult_below h mi limits base frame callers code hr).related, rfl⟩
  · right
    constructor
    · refine ⟨error, hgas.elim Or.inr Or.inl, Or.inr ⟨rfl, .host error.message,
        Exec.commitHost small (some mi) {after.host with lastError := some error} (some after.mem), ?_, ?_⟩⟩
      · simp only [hinvoke, trapWith, callResult]
      · rw [commitHost_host]
        simp only [trapError, hfresh]
    · change List.IsPrefix _ _
      rw [call_logs, call_logs]
      refine ⟨[], ?_⟩
      simpa only [List.append_nil, hinvoke, Budget.resultStore, trapWith] using hlogs

/-- Every continuing actual storage-call transition preserves issue freshness.
Structured trie errors are allowed on terminal traps, and are not assumed absent. -/
theorem advance_next_issue (cfg : WasmConfig) (extra : Nat) (store : Store NearState)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index addr : Nat)
    (keyLen keyPtr valueLen valuePtr : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (metered extra "storage_write" storageWriteFn).toHostFn))
    (hview : store.host.context.isView = false) (after : Config NearState)
    (hnext : (advance cfg (.next (atCode store limits (base ++ args keyLen keyPtr valueLen valuePtr).toArray
      frame callers (.call index :: code)))).1 = .next after) :
    after.store.host.lastExecutionIssue = store.host.lastExecutionIssue := by
  rw [advance_host cfg store mi limits base (args keyLen keyPtr valueLen valuePtr) frame callers code index addr
    (metered extra "storage_write" storageWriteFn) hmodule haddr hfn rfl] at hnext
  cases hop : (chargeHost store.host cfg.regularOpCost).2 with
  | some error =>
    simp only [hop] at hnext
    cases hnext
    rfl
  | none =>
    simp only [hop] at hnext
    cases hi : (metered extra "storage_write" storageWriteFn).invoke
      (hostView (chargedStore store cfg.regularOpCost) mi) (args keyLen keyPtr valueLen valuePtr) with
    | Trap hostAfter message =>
      simp only [hi, callResult, chargeWasm] at hnext
      cases hnext
    | Return values hostAfter =>
      have hf := StorageMeteredBudget.metered_return_issue extra
        (hostView (chargedStore store cfg.regularOpCost) mi) keyLen keyPtr valueLen valuePtr hview values hostAfter hi
      simp only [hi, callResult, chargeWasm] at hnext
      cases hnext
      simpa only [chargeConfig, chargedStore, chargeHost, atCode, commitHost_host, hostView] using hf

end Wasm.Near.MeteredStorageBudget
