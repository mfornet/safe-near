import NearVM.MeteredPureBudget
import NearVM.MeteredTrap

/-!
# From actual host budget replay to a metered machine transition

The bridge resolves the real direct host call, commits its returned memory and
host state, and accounts for both the call opcode and activation charge. The
input instance uses the proved concrete metered host replay. Host gas traps are
classified only with an explicit fresh execution-issue invariant.
-/
namespace Wasm.Near.MeteredHostBudget
open MeteredLogic MeteredPrefix MeteredPureBudget MeteredHosts

/-- The actual host's view of the caller's first memory and host state. -/
def hostView (store : Store NearState) (mi : ModuleInst) : HostStore NearState :=
  ⟨(store.memOf mi).getD (Memory.new 0 none), store.host⟩

theorem hostView_below {small large : Store NearState} (h : StoreBelow small large) (mi : ModuleInst) :
    Budget.StoreBelow (hostView small mi) (hostView large mi) := by
  have hm := congrArg (fun store : Store NearState => store.memOf mi) h.fields
  exact ⟨congrArg (fun mem => mem.getD (Memory.new 0 none)) hm, h.host⟩

/-- Committing equal memory updates retains the entire Wasm environment. -/
theorem commit_below {small large : Store NearState} (h : StoreBelow small large)
    (mi : ModuleInst) {smallAfter largeAfter : HostStore NearState}
    (hafter : Budget.StoreBelow smallAfter largeAfter) :
    StoreBelow (Exec.commitHost small (some mi) smallAfter.host (some smallAfter.mem))
      (Exec.commitHost large (some mi) largeAfter.host (some largeAfter.mem)) := by
  constructor
  · rw [← h.fields, ← hafter.mem]
    simp only [Exec.commitHost, Store.setMemOf]
    cases mi.memAddrs[0]? <;> rfl
  · simpa only [commitHost_host] using hafter.host

/-- Both ways a real host call resumes or terminates the current machine. -/
def callResult (store : Store NearState) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr) :
    HostResult NearState → Machine
  | .Return values after =>
    .next (atCode (Exec.commitHost store (some mi) after.host (some after.mem)) limits
      (base ++ values).toArray frame callers code)
  | .Trap after message =>
    .trap (.host message) (Exec.commitHost store (some mi) after.host (some after.mem))

/-- No host-contract premise: this equation unfolds the actual installed host
function using only the module/function lookup and argument count. -/
theorem step_call (store : Store NearState) (mi : ModuleInst) (limits : ExecLimits)
    (base args : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (fn : NearHostFn NearState)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : args.length = fn.params.length) :
    Exec.step (atCode store limits (base ++ args).toArray frame callers (.call index :: code)) =
      callResult store mi limits base frame callers code (fn.invoke (hostView store mi) args) := by
  cases hi : fn.invoke (hostView store mi) args with
  | Return values after =>
    exact step_call_host store limits base args values frame callers code index addr mi fn after
      hmodule haddr hfn hargs hi
  | Trap after message =>
    exact step_call_host_trap store limits base args frame callers code index addr mi fn after message
      hmodule haddr hfn hargs hi

/-- Any of the concrete input/log/return ResultBelow proofs can use this
operational bridge; the machine retains the same caller stack and control. -/
theorem callResult_below {small large : Store NearState} (h : StoreBelow small large)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr)
    {smallResult largeResult : HostResult NearState} (hr : Budget.ResultBelow smallResult largeResult) :
    MachineBelow (callResult small mi limits base frame callers code smallResult)
      (callResult large mi limits base frame callers code largeResult) := by
  cases hr with
  | returned values hafter => exact .next ⟨commit_below h mi hafter, rfl, rfl⟩
  | trapped message hafter => exact .trapped (.host message) (commit_below h mi hafter)

private theorem call_no_activation (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (limits : ExecLimits) (base args : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (index : Nat) (result : HostResult NearState) :
    frameTransitionGas cfg (atCode store limits (base ++ args).toArray frame callers (.call index :: code))
      (callResult store mi limits base frame callers code result) = 0 := by
  cases result <;> simp [callResult, frameTransitionGas, Config.callDepth, atCode]

/-- The actual metered call transition, with opcode charge before invocation
and zero frame-activation charge after either host exit. -/
theorem advance_host (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) (limits : ExecLimits)
    (base args : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (fn : NearHostFn NearState)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : args.length = fn.params.length) :
    advance cfg (.next (atCode store limits (base ++ args).toArray frame callers (.call index :: code))) =
      match (chargeHost store.host cfg.regularOpCost).2 with
      | some error =>
        (.next (atCode (chargedStore store cfg.regularOpCost) limits (base ++ args).toArray
          frame callers (.call index :: code)), some (.hostError error))
      | none =>
        let next := callResult (chargedStore store cfg.regularOpCost) mi limits base frame callers code
          (fn.invoke (hostView (chargedStore store cfg.regularOpCost) mi) args)
        let charged := chargeWasm next 0
        (charged.1, charged.2.map FunctionCallError.hostError) := by
  have hcost : nextInstructionGas cfg
      (atCode store limits (base ++ args).toArray frame callers (.call index :: code)) = cfg.regularOpCost := by
    simp [nextInstructionGas, Config.nextInstr?, atCode, linearInstruction, loopBackedge]
  simp only [advance, hcost]
  have hs := step_call (chargedStore store cfg.regularOpCost) mi limits base args frame callers code index addr fn
    hmodule haddr hfn hargs
  change Exec.step (chargeConfig
      (atCode store limits (base ++ args).toArray frame callers (.call index :: code)) cfg.regularOpCost).1 = _ at hs
  rw [hs]
  rw [show frameTransitionGas cfg
      (chargeConfig (atCode store limits (base ++ args).toArray frame callers (.call index :: code)) cfg.regularOpCost).1
      (callResult (chargedStore store cfg.regularOpCost) mi limits base frame callers code
        (fn.invoke (hostView (chargedStore store cfg.regularOpCost) mi) args)) = 0 from
    call_no_activation cfg (chargedStore store cfg.regularOpCost) mi limits base args frame callers code index _]
  rfl

private theorem chargeWasm_logs (m : Machine) (cost : Nat) :
    (chargeWasm m cost).1.host.logs = m.host.logs := by cases m <;> rfl

private theorem callResult_logs (store : Store NearState) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (result : HostResult NearState) :
    (callResult store mi limits base frame callers code result).host.logs = (Budget.resultStore result).host.logs := by
  cases result <;> simp only [callResult, StepResult.host, atCode, commitHost_host, Budget.resultStore]

private theorem chargeHost_error_is_gas (host : NearState) (cost : Nat) {error : HostError}
    (herr : (chargeHost host cost).2 = some error) : GasError error := by
  exact (GasCounter.deduct_error_is_gas host.gas cost cost herr).elim Or.inr Or.inl

private theorem chargeWasm_error_is_gas (m : Machine) (cost : Nat) {error : HostError}
    (herr : (chargeWasm m cost).2 = some error) : GasError error := by
  cases m <;> exact chargeHost_error_is_gas _ cost herr

/-- Billing cannot clear, replace or invent the structured host trap cause. -/
private theorem charge_gas_trap (store : Store NearState) (reason : Trap) (error : HostError)
    (cost : Nat) (hgas : GasError error) (hcause : trapError reason store.host = .hostError error) :
    GasFailure ((chargeWasm (.trap reason store) cost).1,
      (chargeWasm (.trap reason store) cost).2.map FunctionCallError.hostError) := by
  cases he : (chargeWasm (.trap reason store) cost).2 with
  | some chargeError =>
    exact ⟨chargeError, chargeWasm_error_is_gas _ cost he, Or.inl rfl⟩
  | none =>
    refine ⟨error, hgas, Or.inr ⟨rfl, reason, chargedStore store cost, rfl, ?_⟩⟩
    exact hcause

private theorem advance_input_logs (cfg : WasmConfig) (extra : Nat) (store : Store NearState)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index addr : Nat) (register : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (metered extra "input" inputFn).toHostFn)) :
    (advance cfg (.next (atCode store limits (base ++ [Value.i64 register]).toArray
      frame callers (.call index :: code)))).1.host.logs = store.host.logs := by
  rw [advance_host cfg store mi limits base [Value.i64 register] frame callers code index addr
    (metered extra "input" inputFn) hmodule haddr hfn rfl]
  cases hop : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => rfl
  | none =>
    rw [chargeWasm_logs, callResult_logs]
    exact (Budget.metered_input_frame (hostView (chargedStore store cfg.regularOpCost) mi) extra register).2

private theorem input_issue (store : HostStore NearState) (extra : Nat) (register : UInt64) :
    (Budget.resultStore ((metered extra "input" inputFn).invoke store [.i64 register])).host.lastExecutionIssue =
      store.host.lastExecutionIssue := by
  have hraw (st : HostStore NearState) :
      (Budget.resultStore (inputFn.invoke st [.i64 register])).host.lastExecutionIssue = st.host.lastExecutionIssue := by
    by_cases hr : register = u64Max
    · subst register
      rw [Input.raw_discard]
      rfl
    · cases hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length with
      | true => rw [Input.raw_ok st register hr hlimit]; rfl
      | false => rw [Input.raw_too_long st register hr hlimit]; rfl
  have hpaid : (Input.paid store).host.lastExecutionIssue = store.host.lastExecutionIssue := by
    have hf := congrArg (fun st : HostStore NearState => st.host.lastExecutionIssue) (Input.paid_frame store)
    exact hf
  rw [Input.metered_eq]
  cases he : (applyCharges store.host [.ext "base", .ext "write_register_base"]).2 with
  | some error => exact hpaid
  | none => exact (hraw (Input.paid store)).trans hpaid

/-- The real input transition preserves freshness of structured execution
issues, so the replay theorem's premise can be maintained at the next step. -/
theorem advance_input_issue (cfg : WasmConfig) (extra : Nat) (store : Store NearState)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index addr : Nat) (register : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (metered extra "input" inputFn).toHostFn)) :
    (advance cfg (.next (atCode store limits (base ++ [Value.i64 register]).toArray
      frame callers (.call index :: code)))).1.host.lastExecutionIssue = store.host.lastExecutionIssue := by
  have hcharge (m : Machine) (cost : Nat) :
      (chargeWasm m cost).1.host.lastExecutionIssue = m.host.lastExecutionIssue := by cases m <;> rfl
  have hcall (source : Store NearState) (result : HostResult NearState) :
      (callResult source mi limits base frame callers code result).host.lastExecutionIssue =
        (Budget.resultStore result).host.lastExecutionIssue := by
    cases result <;> simp only [callResult, StepResult.host, atCode, commitHost_host, Budget.resultStore]
  rw [advance_host cfg store mi limits base [Value.i64 register] frame callers code index addr
    (metered extra "input" inputFn) hmodule haddr hfn rfl]
  cases hop : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => rfl
  | none =>
    rw [hcharge, hcall]
    exact input_issue (hostView (chargedStore store cfg.regularOpCost) mi) extra register

/-- The concrete `env.input` transition satisfies the runner's local budget
simulation. The freshness premise is necessary: `trapError` gives a pre-existing
execution issue precedence over a host's newly recorded gas error. -/
theorem input_replay (cfg : WasmConfig) (extra : Nat) {small large : Store NearState}
    (h : StoreBelow small large) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (register : UInt64)
    (hmodule : small.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : small.funcs[addr]? = some (.host (metered extra "input" inputFn).toHostFn))
    (hissue : small.host.lastExecutionIssue = none) :
    MatchesOrGas MachineBelow
      (advance cfg (.next (atCode small limits (base ++ [Value.i64 register]).toArray
        frame callers (.call index :: code))))
      (advance cfg (.next (atCode large limits (base ++ [Value.i64 register]).toArray
        frame callers (.call index :: code)))) := by
  have hmodules : small.modules = large.modules := by
    have hf := congrArg (fun store : Store NearState => store.modules) h.fields
    exact hf
  have hfuncs : small.funcs = large.funcs := by
    have hf := congrArg (fun store : Store NearState => store.funcs) h.fields
    exact hf
  have hmoduleLarge : large.modules[frame.inst]? = some mi := by rw [← hmodules]; exact hmodule
  have hfnLarge : large.funcs[addr]? = some (.host (metered extra "input" inputFn).toHostFn) := by
    rw [← hfuncs]; exact hfn
  have hs := advance_host cfg small mi limits base [Value.i64 register] frame callers code index addr
    (metered extra "input" inputFn) hmodule haddr hfn rfl
  have hl := advance_host cfg large mi limits base [Value.i64 register] frame callers code index addr
    (metered extra "input" inputFn) hmoduleLarge haddr hfnLarge rfl
  have hlogs : LogPrefix
      (advance cfg (.next (atCode small limits (base ++ [Value.i64 register]).toArray
        frame callers (.call index :: code)))).1
      (advance cfg (.next (atCode large limits (base ++ [Value.i64 register]).toArray
        frame callers (.call index :: code)))).1 := by
    refine ⟨[], ?_⟩
    simpa only [List.append_nil,
      advance_input_logs cfg extra small mi limits base frame callers code index addr register hmodule haddr hfn,
      advance_input_logs cfg extra large mi limits base frame callers code index addr register hmoduleLarge haddr hfnLarge]
      using h.host.logs
  cases hop : (chargeHost small.host cfg.regularOpCost).2 with
  | some error =>
    right
    refine ⟨⟨error, chargeHost_error_is_gas small.host _ hop, Or.inl ?_⟩, hlogs⟩
    simp only [hs, hop]
  | none =>
    have hc := chargedStore_below h cfg.regularOpCost hop
    have hv := hostView_below hc.2 mi
    rcases Budget.metered_input_replay hv extra register with hresult | ⟨error, hgas, hinvoke, _⟩
    · have hstep := callResult_below hc.2 mi limits base frame callers code hresult
      cases hf : (chargeWasm (callResult (chargedStore small cfg.regularOpCost) mi limits base frame callers code
          ((metered extra "input" inputFn).invoke (hostView (chargedStore small cfg.regularOpCost) mi)
            [.i64 register])) 0).2 with
      | some error =>
        right
        refine ⟨⟨error, chargeWasm_error_is_gas _ _ hf, Or.inl ?_⟩, hlogs⟩
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
      apply charge_gas_trap _ _ error 0 (hgas.elim Or.inr Or.inl)
      rw [commitHost_host]
      have hf := congrArg (fun st : HostStore NearState => st.host.lastExecutionIssue)
        (Input.paid_frame (hostView (chargedStore small cfg.regularOpCost) mi))
      have hfresh : (Input.paid (hostView (chargedStore small cfg.regularOpCost) mi)).host.lastExecutionIssue = none :=
        hf.trans hissue
      simp only [trapError, hfresh]

end Wasm.Near.MeteredHostBudget
