import NearVM.MeteredHostBudget
import NearVM.MeteredHosts.LogBudget
import NearVM.MeteredHosts.ReturnBudget

/-!
# Actual output-host transitions under different internal budgets

Both hosts use their concrete decoders, charge plans and functional operations.
The machine theorem includes opcode charging, actual direct-call lookup, memory
commit and the final activation charge. The execution-issue invariant is explicit
and preserved, including on every ordinary and gas failure.
-/
namespace Wasm.Near.MeteredOutputBudget
open MeteredLogic MeteredPrefix MeteredPureBudget MeteredHosts MeteredHostBudget

/-- The two output hosts whose actual implementations have budget replay. -/
inductive OutputOp where
  | logUtf8
  | valueReturn

def OutputOp.name : OutputOp → String
  | .logUtf8 => "log_utf8"
  | .valueReturn => "value_return"

def OutputOp.raw : OutputOp → NearHostFn NearState
  | .logUtf8 => logUtf8Fn
  | .valueReturn => valueReturnFn

def OutputOp.fn (op : OutputOp) (extra : Nat) : NearHostFn NearState :=
  metered extra op.name op.raw

private theorem burnsOnly (op : OutputOp) (st : HostStore NearState) (len ptr : UInt64) :
    ∀ c ∈ chargesBefore op.name st [Value.i64 len, Value.i64 ptr], BurnsOnly c := by
  cases op
  · exact Output.logUtf8_burnsOnly st len ptr
  · exact Output.valueReturn_burnsOnly st len ptr

private theorem paid_issue (op : OutputOp) (st : HostStore NearState) (len ptr : UInt64) :
    (Output.paidStore st (applyCharges st.host
      (chargesBefore op.name st [Value.i64 len, Value.i64 ptr])).1).host.lastExecutionIssue =
      st.host.lastExecutionIssue := by
  have hf := congrArg NearState.lastExecutionIssue (applyCharges_frame st.host
    (chargesBefore op.name st [Value.i64 len, Value.i64 ptr]) (burnsOnly op st len ptr))
  exact hf

private theorem raw_issue (op : OutputOp) (st : HostStore NearState) (len ptr : UInt64) :
    (Budget.resultStore (op.raw.invoke st [Value.i64 len, Value.i64 ptr])).host.lastExecutionIssue =
      st.host.lastExecutionIssue := by
  cases op with
  | logUtf8 =>
    cases hr : (logUtf8Read st len ptr).result with
    | ok msg => rw [show OutputOp.logUtf8.raw = logUtf8Fn from rfl, Output.logUtf8_ok st len ptr msg hr]; rfl
    | error error => rw [show OutputOp.logUtf8.raw = logUtf8Fn from rfl, Output.logUtf8_error st len ptr error hr]; rfl
  | valueReturn =>
    dsimp only [OutputOp.raw, valueReturnFn, checkDataLimit]
    repeat' (first | rfl | split)

/-- Billing and either concrete functional output host preserve the structured
execution issue; decoding, limits and span errors only update `lastError`. -/
theorem host_issue (op : OutputOp) (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) :
    (Budget.resultStore ((op.fn extra).invoke st [Value.i64 len, Value.i64 ptr])).host.lastExecutionIssue =
      st.host.lastExecutionIssue := by
  have hp := paid_issue op st len ptr
  cases op with
  | logUtf8 =>
    rw [show OutputOp.logUtf8.fn extra = metered extra "log_utf8" logUtf8Fn from rfl,
      Output.metered_logUtf8_eq]
    cases hc : applyCharges st.host (chargesBefore "log_utf8" st [Value.i64 len, Value.i64 ptr]) with
    | mk paid error =>
      change (Output.paidStore st (applyCharges st.host
        (chargesBefore "log_utf8" st [Value.i64 len, Value.i64 ptr])).1).host.lastExecutionIssue = _ at hp
      rw [hc] at hp
      cases error with
      | some error => exact hp
      | none => exact (raw_issue .logUtf8 (Output.paidStore st paid) len ptr).trans hp
  | valueReturn =>
    rw [show OutputOp.valueReturn.fn extra = metered extra "value_return" valueReturnFn from rfl,
      Output.metered_valueReturn_eq]
    cases hc : applyCharges st.host (chargesBefore "value_return" st [Value.i64 len, Value.i64 ptr]) with
    | mk paid error =>
      change (Output.paidStore st (applyCharges st.host
        (chargesBefore "value_return" st [Value.i64 len, Value.i64 ptr])).1).host.lastExecutionIssue = _ at hp
      rw [hc] at hp
      cases error with
      | some error => exact hp
      | none =>
        change (Budget.resultStore (match preInvokeError "value_return" (Output.paidStore st paid) [Value.i64 len, Value.i64 ptr] with
          | some error => trapWith (Output.paidStore st paid) error
          | none => valueReturnFn.invoke (Output.paidStore st paid) [Value.i64 len, Value.i64 ptr])).host.lastExecutionIssue = _
        cases preInvokeError "value_return" (Output.paidStore st paid) [Value.i64 len, Value.i64 ptr] with
        | some error => exact hp
        | none => exact (raw_issue .valueReturn (Output.paidStore st paid) len ptr).trans hp

private theorem host_logs (op : OutputOp) (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) :
    List.IsPrefix st.host.logs
      (Budget.resultStore ((op.fn extra).invoke st [Value.i64 len, Value.i64 ptr])).host.logs := by
  cases op with
  | logUtf8 => exact (LogBudget.metered_frame st extra len ptr).2
  | valueReturn =>
    refine ⟨[], ?_⟩
    simpa only [List.append_nil, OutputOp.fn, OutputOp.name, OutputOp.raw] using (ReturnBudget.metered_frame st extra len ptr).2.symm

private theorem host_replay (op : OutputOp) (extra : Nat) {small large : HostStore NearState}
    (h : Budget.StoreBelow small large) (len ptr : UInt64)
    (hissue : small.host.lastExecutionIssue = none) :
    Budget.ResultBelow ((op.fn extra).invoke small [Value.i64 len, Value.i64 ptr])
      ((op.fn extra).invoke large [Value.i64 len, Value.i64 ptr]) ∨
    ∃ error after, GasError error ∧
      (op.fn extra).invoke small [Value.i64 len, Value.i64 ptr] = trapWith after error ∧
      after.host.lastExecutionIssue = none ∧
      List.IsPrefix after.host.logs
        (Budget.resultStore ((op.fn extra).invoke large [Value.i64 len, Value.i64 ptr])).host.logs := by
  have hp := (paid_issue op small len ptr).trans hissue
  cases op with
  | logUtf8 =>
    rcases LogBudget.metered_replay h extra len ptr with hr | ⟨error, hgas, hi, hlogs⟩
    · exact Or.inl hr
    · exact Or.inr ⟨error, _, hgas.elim Or.inr Or.inl, hi, hp, hlogs⟩
  | valueReturn =>
    rcases ReturnBudget.metered_replay h extra len ptr with hr | ⟨error, hgas, hi, hlogs⟩
    · exact Or.inl hr
    · refine Or.inr ⟨error, _, hgas.elim Or.inr Or.inl, hi, hp, [], ?_⟩
      simpa only [List.append_nil, OutputOp.fn, OutputOp.name, OutputOp.raw] using hlogs

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

/-- The complete actual transition only extends logs. This includes all low
billing exits and the high call's possibly successful message append. -/
theorem advance_logs (op : OutputOp) (cfg : WasmConfig) (extra : Nat) (store : Store NearState)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index addr : Nat) (len ptr : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (op.fn extra).toHostFn)) :
    List.IsPrefix store.host.logs
      (advance cfg (.next (atCode store limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
        frame callers (.call index :: code)))).1.host.logs := by
  have hargs : [Value.i64 len, Value.i64 ptr].length = (op.fn extra).params.length := by cases op <;> rfl
  rw [advance_host cfg store mi limits base [Value.i64 len, Value.i64 ptr] frame callers code index addr
    (op.fn extra) hmodule haddr hfn hargs]
  cases hop : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => exact ⟨[], List.append_nil _⟩
  | none =>
    rw [charge_logs, call_logs]
    exact host_logs op extra (hostView (chargedStore store cfg.regularOpCost) mi) len ptr

/-- Freshness is preserved by the actual machine transition, for logging and
return selection with arbitrary fixed/sentinel lengths and pointers. -/
theorem advance_issue (op : OutputOp) (cfg : WasmConfig) (extra : Nat) (store : Store NearState)
    (mi : ModuleInst) (limits : ExecLimits) (base : List Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index addr : Nat) (len ptr : UInt64)
    (hmodule : store.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host (op.fn extra).toHostFn)) :
    (advance cfg (.next (atCode store limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
      frame callers (.call index :: code)))).1.host.lastExecutionIssue = store.host.lastExecutionIssue := by
  have hcharge (m : Machine) (cost : Nat) :
      (chargeWasm m cost).1.host.lastExecutionIssue = m.host.lastExecutionIssue := by cases m <;> rfl
  have hcall (source : Store NearState) (result : HostResult NearState) :
      (callResult source mi limits base frame callers code result).host.lastExecutionIssue =
        (Budget.resultStore result).host.lastExecutionIssue := by
    cases result <;> simp only [callResult, StepResult.host, atCode, commitHost_host, Budget.resultStore]
  have hargs : [Value.i64 len, Value.i64 ptr].length = (op.fn extra).params.length := by cases op <;> rfl
  rw [advance_host cfg store mi limits base [Value.i64 len, Value.i64 ptr] frame callers code index addr
    (op.fn extra) hmodule haddr hfn hargs]
  cases hop : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => rfl
  | none =>
    rw [hcharge, hcall]
    exact host_issue op extra (hostView (chargedStore store cfg.regularOpCost) mi) len ptr

/-- Concrete local machine simulation for the installed `log_utf8` or
`value_return`. Only lookup metadata and a fresh structured execution issue are
premises; the actual host replay, reads and billing are proved in the modules. -/
theorem replay (op : OutputOp) (cfg : WasmConfig) (extra : Nat) {small large : Store NearState}
    (h : StoreBelow small large) (mi : ModuleInst) (limits : ExecLimits)
    (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr)
    (index addr : Nat) (len ptr : UInt64)
    (hmodule : small.modules[frame.inst]? = some mi) (haddr : mi.funcAddrs[index]? = some addr)
    (hfn : small.funcs[addr]? = some (.host (op.fn extra).toHostFn))
    (hissue : small.host.lastExecutionIssue = none) :
    MatchesOrGas MachineBelow
      (advance cfg (.next (atCode small limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
        frame callers (.call index :: code))))
      (advance cfg (.next (atCode large limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
        frame callers (.call index :: code)))) := by
  have hmodules : small.modules = large.modules := by
    have hf := congrArg (fun store : Store NearState => store.modules) h.fields
    exact hf
  have hfuncs : small.funcs = large.funcs := by
    have hf := congrArg (fun store : Store NearState => store.funcs) h.fields
    exact hf
  have hmoduleLarge : large.modules[frame.inst]? = some mi := by rw [← hmodules]; exact hmodule
  have hfnLarge : large.funcs[addr]? = some (.host (op.fn extra).toHostFn) := by
    rw [← hfuncs]; exact hfn
  have hargs : [Value.i64 len, Value.i64 ptr].length = (op.fn extra).params.length := by cases op <;> rfl
  have hs := advance_host cfg small mi limits base [Value.i64 len, Value.i64 ptr] frame callers code index addr
    (op.fn extra) hmodule haddr hfn hargs
  have hl := advance_host cfg large mi limits base [Value.i64 len, Value.i64 ptr] frame callers code index addr
    (op.fn extra) hmoduleLarge haddr hfnLarge hargs
  cases hop : (chargeHost small.host cfg.regularOpCost).2 with
  | some error =>
    right
    refine ⟨⟨error, charge_error small.host _ hop, Or.inl ?_⟩, ?_⟩
    · simp only [hs, hop]
    · change List.IsPrefix _ _
      simp only [hs, hop]
      change List.IsPrefix small.host.logs _
      rw [h.host.logs]
      exact advance_logs op cfg extra large mi limits base frame callers code index addr len ptr
        hmoduleLarge haddr hfnLarge
  | none =>
    have hc := chargedStore_below h cfg.regularOpCost hop
    have hv := hostView_below hc.2 mi
    rcases host_replay op extra hv len ptr hissue with hresult | ⟨error, after, hgas, hinvoke, hfresh, hlogs⟩
    · have hstep := callResult_below hc.2 mi limits base frame callers code hresult
      have hlogs : LogPrefix
          (advance cfg (.next (atCode small limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
            frame callers (.call index :: code)))).1
          (advance cfg (.next (atCode large limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
            frame callers (.call index :: code)))).1 := by
        change List.IsPrefix _ _
        simp only [hs, hl, hop, hc.1, charge_logs]
        refine ⟨[], ?_⟩
        simpa only [List.append_nil] using hstep.related.logs
      cases hf : (chargeWasm (callResult (chargedStore small cfg.regularOpCost) mi limits base frame callers code
          ((op.fn extra).invoke (hostView (chargedStore small cfg.regularOpCost) mi) [Value.i64 len, Value.i64 ptr])) 0).2 with
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
      constructor
      · simp only [hs, hop, hinvoke, trapWith, callResult]
        apply charge_trap _ _ error hgas
        rw [commitHost_host]
        simp only [trapError, hfresh]
      · change List.IsPrefix _ _
        simp only [hs, hl, hop, hc.1, charge_logs, call_logs]
        simpa only [hinvoke, Budget.resultStore, trapWith] using hlogs

end Wasm.Near.MeteredOutputBudget
