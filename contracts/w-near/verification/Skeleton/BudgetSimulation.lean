import Skeleton.Body
import NearVM.MeteredHostBudget
import NearVM.MeteredOutputBudget
import NearVM.MeteredStorageBudget
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Concrete local simulation phases for the walking method

Every source here is an actual suffix of `module.funcs[0]!.body`, with its
concrete operand stack. The only host-specific readiness condition is the
primitive trie condition at the low paid storage call. No whole-run simulation
or abstract host callback is assumed. Initial budget enlargement changes only
the internal gas counter, retaining the complete guest-visible context.
-/
namespace WNear.Skeleton.BudgetSimulation
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget MeteredHostBudget
open MeteredHosts

/-- Auxiliary high budgets leave guest-visible prepaid gas and context fixed. -/
def enlargeHost (host : NearState) (budget : Nat) : NearState :=
  {host with gas := {host.gas with
    prepaid := max host.gas.prepaid budget
    maxBurnt := max host.gas.maxBurnt budget}}

theorem enlargeHost_below (host : NearState) (budget : Nat) :
    Budget.HostBelow host (enlargeHost host budget) :=
  ⟨rfl, GasCounter.below_withLimits host.gas _ _ (Nat.le_max_left _ _) (Nat.le_max_left _ _)⟩

@[simp] theorem enlargeHost_context (host : NearState) (budget : Nat) :
    (enlargeHost host budget).context = host.context := rfl

/-- Any chosen finite high budget can be funded without modifying VMContext. -/
theorem enlarged_initial_credits (cfg : RuntimeConfig) (ctx : VMContext) (raw : List (Near.Bytes × Near.Bytes)) (budget : Nat) :
    (enlargeHost (ctx.toNearState cfg raw) budget).gas.Credits budget := by
  simp only [GasCounter.Credits, enlargeHost, GasCounter.used, VMContext.toNearState, Nat.zero_add]
  exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- Initialization shares actual host metadata and symbolic prepared memory. -/
theorem initialized_below (cfg : RuntimeConfig) (host : NearState) (memory : Memory) (budget : Nat) :
    StoreBelow (initializedStore cfg host memory) (initializedStore cfg (enlargeHost host budget) memory) :=
  ⟨rfl, enlargeHost_below host budget⟩

/-- The actual code suffix, not a separate specification program. -/
def phaseCode (pc : Nat) : List Instr := module.funcs[0]!.body.drop pc

/-- Shared operands at each actual program point. `written` is the discarded
storage return flag; no property of its value is needed for dropping it. -/
def phaseStack (pc : Nat) (written : UInt64) : Array Value :=
  match pc with
  | 1 => #[.i64 0]
  | 3 => #[.i64 1]
  | 4 => #[.i64 1, .i64 0]
  | 5 => #[.i64 1, .i64 0, .i64 u64Max]
  | 6 => #[.i64 1, .i64 0, .i64 u64Max, .i64 0]
  | 7 => #[.i64 1, .i64 0, .i64 u64Max, .i64 0, .i64 u64Max]
  | 8 => #[.i64 written]
  | 10 => #[.i64 5]
  | 11 => #[.i64 5, .i64 1]
  | 13 => #[.i64 u64Max]
  | 14 => #[.i64 u64Max, .i64 0]
  | _ => #[]

def phaseMachine (store : Store NearState) (limits : ExecLimits) (pc : Nat) (written : UInt64) : Machine :=
  .next (atCode store limits (phaseStack pc written) saveFrame [] (phaseCode pc))

/-- Only actual lookup facts about the walking module's four installed hosts. -/
structure Installed (cfg : RuntimeConfig) (store : Store NearState) : Prop where
  module : store.modules[0]? = some moduleInstance
  input : store.funcs[0]? = some (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn)
  storage : store.funcs[1]? = some (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn)
  log : store.funcs[2]? = some (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn)
  returned : store.funcs[3]? = some (.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn)

theorem initialized_installed (cfg : RuntimeConfig) (host : NearState) (memory : Memory) :
    Installed cfg (initializedStore cfg host memory) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Readiness at the precise actual storage-call state after opcode/prebilling. -/
def StorageReady (cfg : RuntimeConfig) (store : Store NearState) : Prop :=
  preInvokeError "storage_write" (MeteredStorageBudget.prechargedHost cfg.wasm store moduleInstance 1 0 u64Max 0)
    (StorageMetered.args 1 0 u64Max 0) = none →
  StorageMeteredBudget.Ready (MeteredStorageBudget.prechargedHost cfg.wasm store moduleInstance 1 0 u64Max 0)
    1 0 u64Max 0

private theorem pure_phase (cfg : RuntimeConfig) {small large : Store NearState} (h : StoreBelow small large)
    (limits : ExecLimits) (pc : Nat) (written : UInt64) (op : PureOp)
    (hcode : phaseCode pc = op.instr :: phaseCode (pc + 1)) :
    MatchesOrGas MachineBelow (advance cfg.wasm (phaseMachine small limits pc written))
      (advance cfg.wasm (phaseMachine large limits pc written)) := by
  simp only [phaseMachine, hcode]
  exact pure_replay cfg.wasm op h limits (phaseStack pc written) saveFrame [] (phaseCode (pc + 1))

/-- All fifteen concrete opcodes and administrative return discharge local
machine budget simulation. Readiness is required only at storage's program
point, and terminal structured issues remain valid matching outcomes. -/
theorem phase_advance_replay (cfg : RuntimeConfig) {small large : Store NearState}
    (h : StoreBelow small large) (hi : Installed cfg small) (limits : ExecLimits)
    (pc : Fin 16) (written : UInt64) (hview : small.host.context.isView = false)
    (hissue : small.host.lastExecutionIssue = none)
    (hstorage : pc.val = 7 → StorageReady cfg small) :
    MatchesOrGas MachineBelow (advance cfg.wasm (phaseMachine small limits pc.val written))
      (advance cfg.wasm (phaseMachine large limits pc.val written)) := by
  fin_cases pc
  · exact pure_phase cfg h limits 0 written (.i64const 0) rfl
  · simp only [phaseMachine, phaseStack]
    rw [show phaseCode 1 = .call 0 :: phaseCode 2 from rfl]
    simpa only [List.nil_append] using
      MeteredHostBudget.input_replay cfg.wasm cfg.fees.numExtraBytesRecord h moduleInstance limits [] saveFrame []
        (phaseCode 2) 0 0 0 hi.module rfl hi.input hissue
  · exact pure_phase cfg h limits 2 written (.i64const 1) rfl
  · exact pure_phase cfg h limits 3 written (.i64const 0) rfl
  · exact pure_phase cfg h limits 4 written (.i64const u64Max) rfl
  · exact pure_phase cfg h limits 5 written (.i64const 0) rfl
  · exact pure_phase cfg h limits 6 written (.i64const u64Max) rfl
  · simp only [phaseMachine, phaseStack]
    rw [show phaseCode 7 = .call 1 :: phaseCode 8 from rfl]
    simpa only [List.nil_append, StorageMetered.args] using
      MeteredStorageBudget.replay cfg.wasm cfg.fees.numExtraBytesRecord h moduleInstance limits [] saveFrame []
        (phaseCode 8) 1 1 1 0 u64Max 0 hi.module rfl hi.storage hview (hstorage rfl) hissue
  · exact pure_phase cfg h limits 8 written .drop rfl
  · exact pure_phase cfg h limits 9 written (.i64const 5) rfl
  · exact pure_phase cfg h limits 10 written (.i64const 1) rfl
  · simp only [phaseMachine, phaseStack]
    rw [show phaseCode 11 = .call 2 :: phaseCode 12 from rfl]
    simpa only [List.nil_append, MeteredOutputBudget.OutputOp.fn,
        MeteredOutputBudget.OutputOp.name, MeteredOutputBudget.OutputOp.raw] using
      MeteredOutputBudget.replay .logUtf8 cfg.wasm cfg.fees.numExtraBytesRecord h moduleInstance limits [] saveFrame []
        (phaseCode 12) 2 2 5 1 hi.module rfl hi.log hissue
  · exact pure_phase cfg h limits 12 written (.i64const u64Max) rfl
  · exact pure_phase cfg h limits 13 written (.i64const 0) rfl
  · simp only [phaseMachine, phaseStack]
    rw [show phaseCode 14 = .call 3 :: phaseCode 15 from rfl]
    simpa only [List.nil_append, MeteredOutputBudget.OutputOp.fn,
        MeteredOutputBudget.OutputOp.name, MeteredOutputBudget.OutputOp.raw] using
      MeteredOutputBudget.replay .valueReturn cfg.wasm cfg.fees.numExtraBytesRecord h moduleInstance limits [] saveFrame []
        (phaseCode 15) 3 3 u64Max 0 hi.module rfl hi.returned hissue
  · exact leave_replay cfg.wasm h limits #[] saveFrame [] rfl

/-- Installed metadata survives every charge, independent of its success. -/
theorem Installed.charged {cfg : RuntimeConfig} {store : Store NearState}
    (h : Installed cfg store) (cost : Nat) : Installed cfg (chargedStore store cost) :=
  ⟨h.module, h.input, h.storage, h.log, h.returned⟩

/-- The concrete host memory commit does not replace module/function slots. -/
theorem Installed.committed {cfg : RuntimeConfig} {store : Store NearState}
    (h : Installed cfg store) (after : HostStore NearState) :
    Installed cfg (Exec.commitHost store (some moduleInstance) after.host (some after.mem)) :=
  ⟨h.module, h.input, h.storage, h.log, h.returned⟩

/-- The finite control/metadata invariant allows terminal outcomes and records
actual suffixes/stacks for continuing configurations. It assumes no gas bound,
trie result, host outcome or whole-run property. -/
def Shape (cfg : RuntimeConfig) (limits : ExecLimits) : Machine → Prop
  | .next c => ∃ pc : Fin 16, ∃ written store,
      c = atCode store limits (phaseStack pc.val written) saveFrame [] (phaseCode pc.val) ∧ Installed cfg store
  | .done _ _ => True
  | .trap _ _ => True

private theorem finish_return_raw (extra : Nat) (name : String) (before : HostStore NearState)
    (args values : List Value) (result : HostResult NearState) (after : HostStore NearState)
    (h : finishMeteredCall extra name before args result = .Return values after) :
    ∃ rawAfter, result = .Return values rawAfter := by
  cases result with
  | Trap st message => cases h
  | Return vals st =>
    unfold finishMeteredCall at h
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk paid error =>
      cases error with
      | some error => simp only [hc, trapWith] at h; cases h
      | none =>
        simp only [hc] at h
        cases hd : deductDeposit name before {st with host := paid} args with
        | mk final error =>
          cases error with
          | some error => simp only [hd, trapWith] at h; cases h
          | none =>
            simp only [hd] at h
            cases he : actionMethodEncodingError name before args with
            | some error => simp only [he, trapWith] at h; cases h
            | none =>
              simp only [he, HostResult.Return.injEq] at h
              rw [← h.1]
              exact ⟨st, rfl⟩

/-- Actual billing, validation and trie preparation do not invent return
operands. A returning wrapper has the same operands as its actual raw host. -/
private theorem metered_return_raw (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (before after : HostStore NearState) (args values : List Value)
    (h : (metered extra name fn).invoke before args = .Return values after) :
    ∃ rawBefore rawAfter, fn.invoke rawBefore args = .Return values rawAfter := by
  unfold metered at h
  dsimp only at h
  split at h
  · simp only [trapWith] at h; cases h
  · split at h
    · cases hc : applyCharges before.host ([.ext "base"] ++
        if name == "promise_return" then [.ext "promise_return"] else []) with
      | mk paid error => simp only [hc, trapWith] at h; cases h
    · cases hc : applyCharges before.host (chargesBefore name before args) with
      | mk paid error =>
        cases error with
        | some error => simp only [hc, trapWith] at h; cases h
        | none =>
          simp only [hc] at h
          change (match preInvokeError name (Output.paidStore before paid) args with
            | some error => trapWith (Output.paidStore before paid) error
            | none => invokeStorageCall extra name fn (Output.paidStore before paid) args) = .Return values after at h
          cases hp : preInvokeError name (Output.paidStore before paid) args with
          | some error => simp only [hp, trapWith] at h; cases h
          | none =>
            simp only [hp] at h
            unfold invokeStorageCall at h
            cases hs : prepareStorageCall name (Output.paidStore before paid) args with
            | mk ready error =>
              cases error with
              | some error => cases error <;> simp only [hs, trapWith] at h <;> cases h
              | none =>
                simp only [hs] at h
                obtain ⟨rawAfter, hraw⟩ := finish_return_raw extra name ready args values (fn.invoke ready args) after h
                exact ⟨ready, rawAfter, hraw⟩

private theorem input_values (extra : Nat) (before after : HostStore NearState) (values : List Value)
    (h : (metered extra "input" inputFn).invoke before [.i64 0] = .Return values after) : values = [] := by
  obtain ⟨rawBefore, rawAfter, hr⟩ := metered_return_raw extra "input" inputFn before after [.i64 0] values h
  dsimp only [inputFn, writeRegisterResult] at hr
  split at hr
  · cases hr; rfl
  · cases hr

private theorem storage_values (extra : Nat) (before after : HostStore NearState) (values : List Value)
    (h : (metered extra "storage_write" storageWriteFn).invoke before
      (StorageMetered.args 1 0 u64Max 0) = .Return values after) : ∃ written : UInt64, values = [.i64 written] := by
  obtain ⟨rawBefore, rawAfter, hr⟩ := metered_return_raw extra "storage_write" storageWriteFn before after
    (StorageMetered.args 1 0 u64Max 0) values h
  dsimp only [storageWriteFn, disallowInView, StorageMetered.args, checkDataLimit, checkedSetRegister?] at hr
  repeat' first
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | cases hr
    | split at hr

private theorem log_values (extra : Nat) (before after : HostStore NearState) (values : List Value)
    (h : (metered extra "log_utf8" logUtf8Fn).invoke before [.i64 5, .i64 1] = .Return values after) : values = [] := by
  obtain ⟨rawBefore, rawAfter, hr⟩ := metered_return_raw extra "log_utf8" logUtf8Fn before after [.i64 5, .i64 1] values h
  dsimp only [logUtf8Fn, appendLogResult] at hr
  split at hr
  · cases hr; rfl
  · cases hr

private theorem return_values (extra : Nat) (before after : HostStore NearState) (values : List Value)
    (h : (metered extra "value_return" valueReturnFn).invoke before [.i64 u64Max, .i64 0] = .Return values after) : values = [] := by
  obtain ⟨rawBefore, rawAfter, hr⟩ := metered_return_raw extra "value_return" valueReturnFn before after [.i64 u64Max, .i64 0] values h
  dsimp only [valueReturnFn, checkDataLimit] at hr
  repeat' first | (cases hr; rfl) | cases hr | split at hr

private theorem pure_shape (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (op : PureOp) (hnext : pc.val + 1 < 16)
    (hcode : phaseCode pc.val = op.instr :: phaseCode (pc.val + 1))
    (hstack : op.stack (phaseStack pc.val written) = phaseStack (pc.val + 1) written) :
    Shape cfg limits (advance cfg.wasm (phaseMachine store limits pc.val written)).1 := by
  simp only [phaseMachine, hcode, advance_pure]
  cases he : (chargeHost store.host cfg.wasm.regularOpCost).2 with
  | some error => exact ⟨pc, written, chargedStore store cfg.wasm.regularOpCost, by rw [hcode], hi.charged _⟩
  | none =>
    refine ⟨⟨pc.val + 1, hnext⟩, written, chargedStore (chargedStore store cfg.wasm.regularOpCost) 0, ?_, (hi.charged _).charged _⟩
    simp only [hstack]
    rfl

private theorem call_shape (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (index addr : Nat)
    (fn : NearHostFn NearState) (input : List Value) (hnext : pc.val + 1 < 16)
    (hcode : phaseCode pc.val = .call index :: phaseCode (pc.val + 1))
    (hstack : phaseStack pc.val written = input.toArray)
    (haddr : moduleInstance.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : input.length = fn.params.length)
    (hvalues : ∀ values after, fn.invoke (hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) input =
      .Return values after → ∃ nextWritten, values.toArray = phaseStack (pc.val + 1) nextWritten) :
    Shape cfg limits (advance cfg.wasm (phaseMachine store limits pc.val written)).1 := by
  simp only [phaseMachine, hcode, hstack]
  have ha := advance_host cfg.wasm store moduleInstance limits [] input saveFrame [] (phaseCode (pc.val + 1))
    index addr fn hi.module haddr hfn hargs
  simp only [List.nil_append] at ha
  rw [ha]
  cases he : (chargeHost store.host cfg.wasm.regularOpCost).2 with
  | some error =>
    refine ⟨pc, written, chargedStore store cfg.wasm.regularOpCost, ?_, hi.charged _⟩
    simp only [hcode, hstack]
  | none =>
    cases hr : fn.invoke (hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) input with
    | Trap after message => trivial
    | Return values after =>
      obtain ⟨nextWritten, hv⟩ := hvalues values after hr
      refine ⟨⟨pc.val + 1, hnext⟩, nextWritten,
        chargedStore (Exec.commitHost (chargedStore store cfg.wasm.regularOpCost)
          (some moduleInstance) after.host (some after.mem)) 0, ?_, ((hi.charged _).committed after).charged _⟩
      simp only [List.nil_append, hv]
      rfl

/-- The control/metadata phase invariant is closed by every actual transition,
including gas-stopped same-phase configurations and all host/trie trap exits.
Host result shapes are proved from the four actual raw implementations. -/
theorem phase_shape_closed (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) :
    Shape cfg limits (advance cfg.wasm (phaseMachine store limits pc.val written)).1 := by
  fin_cases pc
  · exact pure_shape cfg store hi limits 0 written (.i64const 0) (by decide) rfl rfl
  · apply call_shape cfg store hi limits 1 written 0 0
      (metered cfg.fees.numExtraBytesRecord "input" inputFn) [.i64 0] (by decide) rfl rfl rfl hi.input rfl
    intro values after hr
    rw [input_values _ _ _ _ hr]
    exact ⟨written, rfl⟩
  · exact pure_shape cfg store hi limits 2 written (.i64const 1) (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 3 written (.i64const 0) (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 4 written (.i64const u64Max) (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 5 written (.i64const 0) (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 6 written (.i64const u64Max) (by decide) rfl rfl
  · apply call_shape cfg store hi limits 7 written 1 1
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn)
      (StorageMetered.args 1 0 u64Max 0) (by decide) rfl rfl rfl hi.storage rfl
    intro values after hr
    obtain ⟨flag, hv⟩ := storage_values _ _ _ _ hr
    exact ⟨flag, by rw [hv]; rfl⟩
  · exact pure_shape cfg store hi limits 8 written .drop (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 9 written (.i64const 5) (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 10 written (.i64const 1) (by decide) rfl rfl
  · apply call_shape cfg store hi limits 11 written 2 2
      (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn) [.i64 5, .i64 1]
      (by decide) rfl rfl rfl hi.log rfl
    intro values after hr
    rw [log_values _ _ _ _ hr]
    exact ⟨written, rfl⟩
  · exact pure_shape cfg store hi limits 12 written (.i64const u64Max) (by decide) rfl rfl
  · exact pure_shape cfg store hi limits 13 written (.i64const 0) (by decide) rfl rfl
  · apply call_shape cfg store hi limits 14 written 3 3
      (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn) [.i64 u64Max, .i64 0]
      (by decide) rfl rfl rfl hi.returned rfl
    intro values after hr
    rw [return_values _ _ _ _ hr]
    exact ⟨written, rfl⟩
  · unfold phaseMachine
    have hc : nextInstructionGas cfg.wasm (atCode store limits (phaseStack 15 written) saveFrame [] (phaseCode 15)) = 0 := rfl
    simp only [advance, hc]
    rw [show chargeConfig (atCode store limits (phaseStack 15 written) saveFrame [] (phaseCode 15)) 0 =
      (atCode (chargedStore store 0) limits (phaseStack 15 written) saveFrame [] (phaseCode 15),
        (chargeHost store.host 0).2) from rfl]
    cases he : (chargeHost store.host 0).2 with
    | some error => exact ⟨15, written, chargedStore store 0, rfl, hi.charged _⟩
    | none => trivial

/-- A genuine closed invariant for the runner's fuel induction, proved by
concrete phase cases rather than supplied as a whole-run assumption. -/
theorem shape_advanceInvariant (cfg : RuntimeConfig) (limits : ExecLimits) :
    AdvanceInvariant cfg.wasm (Shape cfg limits) := by
  intro m hm
  cases m with
  | done values store => trivial
  | trap reason store => trivial
  | next c =>
    obtain ⟨pc, written, store, rfl, hi⟩ := hm
    exact phase_shape_closed cfg store hi limits pc written

private theorem charge_logs (m : Machine) (cost : Nat) :
    (chargeWasm m cost).1.host.logs = m.host.logs := by cases m <;> rfl

private theorem call_logs (store : Store NearState) (limits : ExecLimits) (code : List Instr)
    (result : HostResult NearState) :
    (callResult store moduleInstance limits [] saveFrame [] code result).host.logs =
      (Budget.resultStore result).host.logs := by
  cases result <;> simp only [callResult, StepResult.host, atCode, commitHost_host, Budget.resultStore]

private theorem pure_phase_logs (cfg : RuntimeConfig) (store : Store NearState) (limits : ExecLimits)
    (pc : Nat) (written : UInt64) (op : PureOp)
    (hcode : phaseCode pc = op.instr :: phaseCode (pc + 1)) :
    LogPrefix (phaseMachine store limits pc written) (advance cfg.wasm (phaseMachine store limits pc written)).1 := by
  change List.IsPrefix store.host.logs _
  simp only [phaseMachine, hcode, advance_pure_logs]
  exact ⟨[], List.append_nil _⟩

private theorem host_phase_logs (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Nat) (written : UInt64) (index addr : Nat) (fn : NearHostFn NearState)
    (input : List Value) (hcode : phaseCode pc = .call index :: phaseCode (pc + 1))
    (hstack : phaseStack pc written = input.toArray) (haddr : moduleInstance.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : input.length = fn.params.length)
    (hlogs : ∀ before, List.IsPrefix before.host.logs (Budget.resultStore (fn.invoke before input)).host.logs) :
    LogPrefix (phaseMachine store limits pc written) (advance cfg.wasm (phaseMachine store limits pc written)).1 := by
  change List.IsPrefix store.host.logs _
  simp only [phaseMachine, hcode, hstack]
  have ha := advance_host cfg.wasm store moduleInstance limits [] input saveFrame [] (phaseCode (pc + 1))
    index addr fn hi.module haddr hfn hargs
  simp only [List.nil_append] at ha
  rw [ha]
  cases he : (chargeHost store.host cfg.wasm.regularOpCost).2 with
  | some error => exact ⟨[], List.append_nil _⟩
  | none =>
    rw [charge_logs, call_logs]
    exact hlogs (hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance)

private theorem storage_logs (extra : Nat) (before : HostStore NearState) :
    (Budget.resultStore ((metered extra "storage_write" storageWriteFn).invoke before
      (StorageMetered.args 1 0 u64Max 0))).host.logs = before.host.logs := by
  cases hv : before.host.context.isView with
  | false => exact StorageMeteredBudget.metered_logs extra before 1 0 u64Max 0 hv
  | true =>
    have hf := congrArg NearState.logs (applyCharges_frame before.host [.ext "base"]
      (by simp [BurnsOnly]))
    simp only [metered, show deprecatedRuntimeHost "storage_write" = false by decide,
      hv, show viewRestrictedHost "storage_write" = true by decide, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      show ("storage_write" == "promise_return") = false by decide, List.append_nil]
    cases hc : applyCharges before.host [.ext "base"] with
    | mk paid error =>
      rw [hc] at hf
      exact hf

/-- Log monotonicity at every concrete phase, including ordinary validation,
structured trie failures and view-prohibited storage calls. -/
theorem phase_logs (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) :
    LogPrefix (phaseMachine store limits pc.val written)
      (advance cfg.wasm (phaseMachine store limits pc.val written)).1 := by
  fin_cases pc
  · exact pure_phase_logs cfg store limits 0 written (.i64const 0) rfl
  · apply host_phase_logs cfg store hi limits 1 written 0 0
      (metered cfg.fees.numExtraBytesRecord "input" inputFn) [.i64 0] rfl rfl rfl hi.input rfl
    intro before
    refine ⟨[], ?_⟩
    simpa only [List.append_nil] using (Budget.metered_input_frame before cfg.fees.numExtraBytesRecord 0).2.symm
  · exact pure_phase_logs cfg store limits 2 written (.i64const 1) rfl
  · exact pure_phase_logs cfg store limits 3 written (.i64const 0) rfl
  · exact pure_phase_logs cfg store limits 4 written (.i64const u64Max) rfl
  · exact pure_phase_logs cfg store limits 5 written (.i64const 0) rfl
  · exact pure_phase_logs cfg store limits 6 written (.i64const u64Max) rfl
  · apply host_phase_logs cfg store hi limits 7 written 1 1
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn)
      (StorageMetered.args 1 0 u64Max 0) rfl rfl rfl hi.storage rfl
    intro before
    refine ⟨[], ?_⟩
    simpa only [List.append_nil] using (storage_logs cfg.fees.numExtraBytesRecord before).symm
  · exact pure_phase_logs cfg store limits 8 written .drop rfl
  · exact pure_phase_logs cfg store limits 9 written (.i64const 5) rfl
  · exact pure_phase_logs cfg store limits 10 written (.i64const 1) rfl
  · apply host_phase_logs cfg store hi limits 11 written 2 2
      (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn) [.i64 5, .i64 1] rfl rfl rfl hi.log rfl
    intro before
    exact (LogBudget.metered_frame before cfg.fees.numExtraBytesRecord 5 1).2
  · exact pure_phase_logs cfg store limits 12 written (.i64const u64Max) rfl
  · exact pure_phase_logs cfg store limits 13 written (.i64const 0) rfl
  · apply host_phase_logs cfg store hi limits 14 written 3 3
      (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn) [.i64 u64Max, .i64 0] rfl rfl rfl hi.returned rfl
    intro before
    refine ⟨[], ?_⟩
    simpa only [List.append_nil] using (ReturnBudget.metered_frame before cfg.fees.numExtraBytesRecord u64Max 0).2.symm
  · change List.IsPrefix store.host.logs _
    unfold phaseMachine
    have hc : nextInstructionGas cfg.wasm (atCode store limits (phaseStack 15 written) saveFrame [] (phaseCode 15)) = 0 := rfl
    simp only [advance, hc]
    rw [show chargeConfig (atCode store limits (phaseStack 15 written) saveFrame [] (phaseCode 15)) 0 =
      (atCode (chargedStore store 0) limits (phaseStack 15 written) saveFrame [] (phaseCode 15),
        (chargeHost store.host 0).2) from rfl]
    cases he : (chargeHost store.host 0).2 with
    | some error => exact ⟨[], List.append_nil _⟩
    | none => exact ⟨[], List.append_nil _⟩

/-- Log monotonicity is discharged on the proved closed phase invariant. -/
theorem shape_logsMonotone (cfg : RuntimeConfig) (limits : ExecLimits) :
    LogsMonotone cfg.wasm (Shape cfg limits) := by
  intro m hm
  cases m with
  | done values store => exact ⟨[], List.append_nil _⟩
  | trap reason store => exact ⟨[], List.append_nil _⟩
  | next c =>
    obtain ⟨pc, written, store, rfl, hi⟩ := hm
    exact phase_logs cfg store hi limits pc written

/-- Concrete shape and installed metadata survive every actual runner prefix,
including fuel and gas stops. This is a proved invariant, not a callback. -/
theorem run_shape (cfg : RuntimeConfig) (limits : ExecLimits) (fuel : Nat) (m : Machine)
    (hm : Shape cfg limits m) : Shape cfg limits (runMetered cfg.wasm fuel m).1 := by
  induction fuel generalizing m with
  | zero => cases m <;> exact hm
  | succ fuel ih =>
    rw [MeteredPrefix.run_succ]
    cases he : (advance cfg.wasm m).2 with
    | some error => exact shape_advanceInvariant cfg limits m hm
    | none => exact ih _ (shape_advanceInvariant cfg limits m hm)

/-- Log prefixes of the actual walking body require no whole-run premise. -/
theorem run_logs (cfg : RuntimeConfig) (limits : ExecLimits) (fuel : Nat) (m : Machine)
    (hm : Shape cfg limits m) : LogPrefix m (runMetered cfg.wasm fuel m).1 :=
  run_logs_monotone cfg.wasm (Shape cfg limits) (shape_advanceInvariant cfg limits)
    (shape_logsMonotone cfg limits) fuel m hm

end WNear.Skeleton.BudgetSimulation
