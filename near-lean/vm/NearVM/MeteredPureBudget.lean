import NearVM.MeteredPrefix
import NearVM.MeteredRules
import NearVM.MeteredHosts.Budget

/-!
# Budget compatibility for pure skeleton instructions

Stores share their entire Wasm environment and functional host fields. The only
differences are internal gas limits and billing profiles. Actual opcode charges,
pure interpreter transitions and activation charges are compared locally.
-/
namespace Wasm.Near.MeteredPureBudget
open MeteredLogic MeteredPrefix

abbrev HostBelow := MeteredHosts.Budget.HostBelow

/-- All Wasm resources and installed host functions are identical. -/
structure StoreBelow (small large : Store NearState) : Prop where
  fields : { small with host := large.host } = large
  host : HostBelow small.host large.host

structure ConfigBelow (small large : Config NearState) : Prop where
  store : StoreBelow small.store large.store
  thread : small.thread = large.thread
  limits : small.limits = large.limits

/-- Equal running control or terminal values/traps, with related stores. -/
inductive MachineBelow : Machine → Machine → Prop
  | next {small large : Config NearState} (h : ConfigBelow small large) :
      MachineBelow (.next small) (.next large)
  | done {small large : Store NearState} (values : List Value) (h : StoreBelow small large) :
      MachineBelow (.done values small) (.done values large)
  | trapped {small large : Store NearState} (reason : Trap) (h : StoreBelow small large) :
      MachineBelow (.trap reason small) (.trap reason large)

theorem MachineBelow.related {small large : Machine} (h : MachineBelow small large) :
    Related MachineBelow small large := by
  cases h with
  | next h => exact ⟨.next h, rfl, h.store.host.context, h.store.host.logs, h.store.host.gas⟩
  | done values h => exact ⟨.done values h, rfl, h.host.context, h.host.logs, h.host.gas⟩
  | trapped reason h => exact ⟨.trapped reason h, rfl, h.host.context, h.host.logs, h.host.gas⟩

/-- The real Wasm instruction charge respects larger internal limits. -/
theorem chargeHost_below {small large : NearState} (h : HostBelow small large) (cost : Nat)
    (hok : (chargeHost small cost).2 = none) :
    (chargeHost large cost).2 = none ∧ HostBelow (chargeHost small cost).1 (chargeHost large cost).1 := by
  have hg := h.gas.burn cost hok
  exact ⟨hg.1, h.fields, hg.2⟩

private theorem StoreBelow.withHosts {small large : Store NearState} (h : StoreBelow small large)
    {smallHost largeHost : NearState} (hhost : HostBelow smallHost largeHost) :
    StoreBelow { small with host := smallHost } { large with host := largeHost } := by
  have hf := congrArg (fun store : Store NearState => { store with host := largeHost }) h.fields
  exact ⟨hf, hhost⟩

theorem chargedStore_below {small large : Store NearState} (h : StoreBelow small large) (cost : Nat)
    (hok : (chargeHost small.host cost).2 = none) :
    (chargeHost large.host cost).2 = none ∧
      StoreBelow (chargedStore small cost) (chargedStore large cost) := by
  have hc := chargeHost_below h.host cost hok
  exact ⟨hc.1, h.withHosts hc.2⟩

theorem chargeConfig_below {small large : Config NearState} (h : ConfigBelow small large) (cost : Nat)
    (hok : (chargeConfig small cost).2 = none) :
    (chargeConfig large cost).2 = none ∧
      ConfigBelow (chargeConfig small cost).1 (chargeConfig large cost).1 := by
  have hc := chargedStore_below h.store cost hok
  exact ⟨hc.1, hc.2, h.thread, h.limits⟩

/-- Activation/entry charging works for all related machine shapes. -/
theorem chargeWasm_below {small large : Machine} (h : MachineBelow small large) (cost : Nat)
    (hok : (chargeWasm small cost).2 = none) :
    (chargeWasm large cost).2 = none ∧
      MachineBelow (chargeWasm small cost).1 (chargeWasm large cost).1 := by
  cases h with
  | next h =>
    have hc := chargeConfig_below h cost hok
    exact ⟨hc.1, .next hc.2⟩
  | done values h =>
    have hc := chargedStore_below h cost hok
    exact ⟨hc.1, .done values hc.2⟩
  | trapped reason h =>
    have hc := chargedStore_below h cost hok
    exact ⟨hc.1, .trapped reason hc.2⟩

/-- Both actual skeleton operations have a fixed ordinary opcode charge. -/
inductive PureOp where
  | i64const (value : UInt64)
  | drop

def PureOp.instr : PureOp → Instr
  | .i64const value => .i64_const value
  | .drop => .drop

def PureOp.stack : PureOp → Array Value → Array Value
  | .i64const value, stack => stack.push (.i64 value)
  | .drop, stack => stack.pop

/-- Concrete interpreter semantics: caller frames, locals, labels and all
resources are preserved; only the operand stack and code advance. -/
theorem step_pure (op : PureOp) (store : Store NearState) (limits : ExecLimits)
    (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr) :
    Exec.step (atCode store limits stack frame callers (op.instr :: code)) =
      .next (atCode store limits (op.stack stack) frame callers code) := by
  cases op <;> rfl

theorem nextInstructionGas_pure (cfg : WasmConfig) (op : PureOp) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) :
    nextInstructionGas cfg (atCode store limits stack frame callers (op.instr :: code)) =
      cfg.regularOpCost := by
  cases op <;>
    simp [PureOp.instr, nextInstructionGas, Config.nextInstr?, atCode, linearInstruction, loopBackedge]

/-- Actual pure transitions preserve the store relation and identical control. -/
theorem step_pure_below (op : PureOp) {small large : Store NearState} (h : StoreBelow small large)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) :
    MachineBelow (Exec.step (atCode small limits stack frame callers (op.instr :: code)))
      (Exec.step (atCode large limits stack frame callers (op.instr :: code))) := by
  rw [step_pure, step_pure]
  exact .next ⟨h, rfl, rfl⟩

/-- Expand one actual pure transition, including the zero activation charge. -/
theorem advance_pure (cfg : WasmConfig) (op : PureOp) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) :
    advance cfg (.next (atCode store limits stack frame callers (op.instr :: code))) =
      match (chargeHost store.host cfg.regularOpCost).2 with
      | some error =>
        (.next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers (op.instr :: code)),
          some (.hostError error))
      | none =>
        let charged := chargeWasm
          (.next (atCode (chargedStore store cfg.regularOpCost) limits (op.stack stack) frame callers code)) 0
        (charged.1, charged.2.map FunctionCallError.hostError) := by
  simp only [advance, nextInstructionGas_pure]
  have hs : Exec.step (chargeConfig
      (atCode store limits stack frame callers (op.instr :: code)) cfg.regularOpCost).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (op.stack stack) frame callers code) :=
    step_pure op (chargedStore store cfg.regularOpCost) limits stack frame callers code
  rw [hs]
  have hf : frameTransitionGas cfg
      (chargeConfig (atCode store limits stack frame callers (op.instr :: code)) cfg.regularOpCost).1
      (.next (atCode (chargedStore store cfg.regularOpCost) limits (op.stack stack) frame callers code)) = 0 := by
    simp [frameTransitionGas, Config.callDepth, chargeConfig, atCode]
  rw [hf]
  rfl

private theorem chargeWasm_logs (m : Machine) (cost : Nat) :
    (chargeWasm m cost).1.host.logs = m.host.logs := by
  cases m <;> rfl

/-- None of the charge/step/activation exits changes logs. -/
theorem advance_pure_logs (cfg : WasmConfig) (op : PureOp) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) :
    (advance cfg (.next (atCode store limits stack frame callers (op.instr :: code)))).1.host.logs =
      store.host.logs := by
  rw [advance_pure]
  cases he : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => rfl
  | none => exact chargeWasm_logs _ 0

private theorem chargeHost_error_is_gas (host : NearState) (cost : Nat) {error : HostError}
    (herr : (chargeHost host cost).2 = some error) : GasError error := by
  have hg := GasCounter.deduct_error_is_gas host.gas cost cost herr
  exact hg.elim Or.inr Or.inl

private theorem chargeWasm_error_is_gas (m : Machine) (cost : Nat) {error : HostError}
    (herr : (chargeWasm m cost).2 = some error) : GasError error := by
  cases m <;> exact chargeHost_error_is_gas _ cost herr

/-- Actual local compatibility for each skeleton pure opcode, with a protocol
gas failure and matching log prefix when the low budget cannot pay a charge. -/
theorem pure_replay (cfg : WasmConfig) (op : PureOp) {small large : Store NearState}
    (h : StoreBelow small large) (limits : ExecLimits) (stack : Array Value)
    (frame : CallFrame) (callers : List CallFrame) (code : List Instr) :
    MatchesOrGas MachineBelow
      (advance cfg (.next (atCode small limits stack frame callers (op.instr :: code))))
      (advance cfg (.next (atCode large limits stack frame callers (op.instr :: code)))) := by
  have hlogs : LogPrefix
      (advance cfg (.next (atCode small limits stack frame callers (op.instr :: code)))).1
      (advance cfg (.next (atCode large limits stack frame callers (op.instr :: code)))).1 := by
    refine ⟨[], ?_⟩
    simpa only [List.append_nil, advance_pure_logs] using h.host.logs
  cases hop : (chargeHost small.host cfg.regularOpCost).2 with
  | some error =>
    right
    refine ⟨⟨error, chargeHost_error_is_gas small.host _ hop, Or.inl ?_⟩, hlogs⟩
    simp only [advance_pure, hop]
  | none =>
    have hc := chargedStore_below h cfg.regularOpCost hop
    have hs := step_pure_below op hc.2 limits stack frame callers code
    rw [step_pure, step_pure] at hs
    cases hf : (chargeWasm
        (.next (atCode (chargedStore small cfg.regularOpCost) limits (op.stack stack) frame callers code)) 0).2 with
    | some error =>
      right
      refine ⟨⟨error, chargeWasm_error_is_gas _ _ hf, Or.inl ?_⟩, hlogs⟩
      simp only [advance_pure, hop, hf, Option.map_some]
    | none =>
      have hframe := chargeWasm_below hs 0 hf
      left
      constructor
      · simpa only [advance_pure, hop, hc.1] using hframe.2.related
      · simp only [advance_pure, hop, hc.1, hf, hframe.1, Option.map_none]

/-- Finishing a frame uses the same operand results and caller continuation
under either budget, including returning from the outermost frame. -/
theorem step_leave_below {small large : Store NearState} (h : StoreBelow small large)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (hlabels : frame.labels = []) :
    MachineBelow (Exec.step (atCode small limits stack frame callers []))
      (Exec.step (atCode large limits stack frame callers [])) := by
  cases callers with
  | nil =>
    simp only [Exec.step, atCode, hlabels, Exec.leave]
    exact .done _ h
  | cons caller callers =>
    simp only [Exec.step, atCode, hlabels, Exec.leave]
    exact .next ⟨h, rfl, rfl⟩

private theorem leave_no_activation (cfg : WasmConfig) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (hlabels : frame.labels = []) :
    frameTransitionGas cfg (atCode store limits stack frame callers [])
      (Exec.step (atCode store limits stack frame callers [])) = 0 := by
  cases callers <;>
    simp [Exec.step, atCode, hlabels, Exec.leave, frameTransitionGas, Config.callDepth]
  omega

private theorem step_leave_logs (store : Store NearState) (limits : ExecLimits)
    (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (hlabels : frame.labels = []) :
    (Exec.step (atCode store limits stack frame callers [])).host.logs = store.host.logs := by
  cases callers <;> simp only [Exec.step, atCode, hlabels, Exec.leave, StepResult.host]

private theorem advance_leave (cfg : WasmConfig) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (hlabels : frame.labels = []) :
    advance cfg (.next (atCode store limits stack frame callers [])) =
      match (chargeHost store.host 0).2 with
      | some error =>
        (.next (atCode (chargedStore store 0) limits stack frame callers []), some (.hostError error))
      | none =>
        let charged := chargeWasm (Exec.step (atCode (chargedStore store 0) limits stack frame callers [])) 0
        (charged.1, charged.2.map FunctionCallError.hostError) := by
  simp only [advance, show nextInstructionGas cfg (atCode store limits stack frame callers []) = 0 from rfl]
  rw [show frameTransitionGas cfg (chargeConfig (atCode store limits stack frame callers []) 0).1
    (Exec.step (chargeConfig (atCode store limits stack frame callers []) 0).1) = 0 from
      leave_no_activation cfg (chargedStore store 0) limits stack frame callers hlabels]
  rfl

private theorem advance_leave_logs (cfg : WasmConfig) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (hlabels : frame.labels = []) :
    (advance cfg (.next (atCode store limits stack frame callers []))).1.host.logs = store.host.logs := by
  rw [advance_leave cfg store limits stack frame callers hlabels]
  cases he : (chargeHost store.host 0).2 with
  | some error => rfl
  | none => exact (chargeWasm_logs _ 0).trans (step_leave_logs _ limits stack frame callers hlabels)

/-- Administrative return also discharges the local simulation: no opcode or
activation cost is invented, and either the same values/caller resume or the
actual counter rejects a zero charge on an already invalid input counter. -/
theorem leave_replay (cfg : WasmConfig) {small large : Store NearState}
    (h : StoreBelow small large) (limits : ExecLimits) (stack : Array Value)
    (frame : CallFrame) (callers : List CallFrame) (hlabels : frame.labels = []) :
    MatchesOrGas MachineBelow
      (advance cfg (.next (atCode small limits stack frame callers [])))
      (advance cfg (.next (atCode large limits stack frame callers []))) := by
  have hlogs : LogPrefix
      (advance cfg (.next (atCode small limits stack frame callers []))).1
      (advance cfg (.next (atCode large limits stack frame callers []))).1 := by
    refine ⟨[], ?_⟩
    simpa only [List.append_nil, advance_leave_logs cfg _ limits stack frame callers hlabels] using h.host.logs
  cases hop : (chargeHost small.host 0).2 with
  | some error =>
    right
    refine ⟨⟨error, chargeHost_error_is_gas small.host _ hop, Or.inl ?_⟩, hlogs⟩
    simp only [advance_leave cfg _ limits stack frame callers hlabels, hop]
  | none =>
    have hc := chargedStore_below h 0 hop
    have hs := step_leave_below hc.2 limits stack frame callers hlabels
    cases hf : (chargeWasm (Exec.step (atCode (chargedStore small 0) limits stack frame callers [])) 0).2 with
    | some error =>
      right
      refine ⟨⟨error, chargeWasm_error_is_gas _ _ hf, Or.inl ?_⟩, hlogs⟩
      simp only [advance_leave cfg _ limits stack frame callers hlabels, hop, hf, Option.map_some]
    | none =>
      have hframe := chargeWasm_below hs 0 hf
      left
      constructor
      · simpa only [advance_leave cfg _ limits stack frame callers hlabels, hop, hc.1] using hframe.2.related
      · simp only [advance_leave cfg _ limits stack frame callers hlabels, hop, hc.1, hf, hframe.1, Option.map_none]

end Wasm.Near.MeteredPureBudget
