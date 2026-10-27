import Skeleton.BudgetSimulation
import Skeleton.Progress
import Skeleton.EmptyStorage
import NearVM.MeteredHosts.StorageFrame
import NearVM.MeteredHosts.StorageReturnFrame

/-!
# Closed functional resources and whole-body budget replay

The pre-write view forgets only billing, the synchronized used-gas field and
register initialization. It retains the original storage/trie/configuration,
input, view mode and structured issue. Primitive storage readiness is derived
from that view, prepared memory, register zero and the original empty-base WF.
Actual continuing phases close the functional invariant; the existing runner
simulation then yields matching whole-body executions or a protocol gas abort
with prefix logs, while keeping the guest-visible VMContext fixed.
-/
namespace WNear.Skeleton.FunctionalInvariant
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget MeteredHostBudget NearInterface
open MeteredHosts BudgetSimulation

/-- The fields that input and pre-write pure opcodes cannot change. -/
def preView (host : NearState) : NearState :=
  {host with
    gas := {}
    gasProfile := {}
    actionProfile := []
    registers := (fun _ => none)
    context := {host.context with usedGas := 0}}

def PreEq (before after : NearState) : Prop := preView after = preView before

namespace PreEq

theorem refl (host : NearState) : PreEq host host := rfl

theorem trans {before middle after : NearState} (h : PreEq before middle) (h' : PreEq middle after) :
    PreEq before after := Eq.trans h' h

theorem charged (host : NearState) (cost : Nat) : PreEq host (chargeHost host cost).1 := rfl

theorem enlarged (host : NearState) (budget : Nat) : PreEq host (enlargeHost host budget) := rfl

theorem charges (host : NearState) (charges : List Charge) (hburn : ∀ c ∈ charges, BurnsOnly c) :
    PreEq host (applyCharges host charges).1 := by
  have hf := congrArg preView (applyCharges_frame host charges hburn)
  simpa only [PreEq, preView] using hf

theorem paid (before : HostStore NearState) (charges : List Charge) (hburn : ∀ c ∈ charges, BurnsOnly c) :
    PreEq before.host (Output.paidStore before (applyCharges before.host charges).1).host := by
  exact PreEq.charges before.host charges hburn

theorem input {before after : NearState} (h : PreEq before after) : after.context.input = before.context.input := by
  have hf := congrArg (fun host : NearState => host.context.input) h
  exact hf

theorem current {before after : NearState} (h : PreEq before after) :
    after.context.currentAccountId = before.context.currentAccountId := by
  have hf := congrArg (fun host : NearState => host.context.currentAccountId) h
  exact hf

theorem isView {before after : NearState} (h : PreEq before after) : after.context.isView = before.context.isView := by
  have hf := congrArg (fun host : NearState => host.context.isView) h
  exact hf

theorem issue {before after : NearState} (h : PreEq before after) : after.lastExecutionIssue = before.lastExecutionIssue := by
  have hf := congrArg NearState.lastExecutionIssue h
  exact hf

theorem storage {before after : NearState} (h : PreEq before after) : after.storage = before.storage := by
  have hf := congrArg NearState.storage h
  exact hf

theorem accounting {before after : NearState} (h : PreEq before after) : after.storageAccounting = before.storageAccounting := by
  have hf := congrArg NearState.storageAccounting h
  exact hf

theorem config {before after : NearState} (h : PreEq before after) : after.config = before.config := by
  have hf := congrArg NearState.config h
  exact hf

theorem proof {before after : NearState} (h : PreEq before after) : after.storageProofSize = before.storageProofSize := by
  have hf := congrArg NearState.storageProofSize h
  exact hf

end PreEq

/-- A returning actual input call installs register zero and preserves every
pre-write functional field and memory. No credit or invocation premise is used
to assert that it returns; the implication classifies an actual returned exit. -/
theorem input_return_frame (extra : Nat) (before after : HostStore NearState) (values : List Value)
    (hreturn : (metered extra "input" inputFn).invoke before [.i64 0] = .Return values after) :
    after.mem = before.mem ∧ PreEq before.host after.host ∧
      after.host.registers 0 = some before.host.context.input := by
  have hp : PreEq before.host (Input.paid before).host := by
    have hf := congrArg (fun st : HostStore NearState => preView st.host) (Input.paid_frame before)
    simpa only [PreEq, preView] using hf
  rw [Input.metered_eq] at hreturn
  cases hc : (applyCharges before.host [.ext "base", .ext "write_register_base"]).2 with
  | some error => simp only [hc, trapWith] at hreturn; cases hreturn
  | none =>
    simp only [hc] at hreturn
    cases hl : withinLimit (Input.paid before).host.config.maxRegisterLen (Input.paid before).host.context.input.length with
    | false =>
      rw [Input.raw_too_long _ 0 (by decide +kernel) hl] at hreturn
      cases hreturn
    | true =>
      rw [Input.raw_ok _ 0 (by decide +kernel) hl] at hreturn
      cases hreturn
      refine ⟨rfl, ?_, ?_⟩
      · exact hp
      · simp only [NearState.setRegister, UInt64.toNat_zero, ↓reduceIte, Input.paid_input]

/-- Original host state, with original VMContext and internal initial limits. -/
def origin (ctx : Context) (raw : Storage) : NearState :=
  (Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw

structure BeforeWrite (ctx : Context) (raw : Storage) (before : HostStore NearState) : Prop where
  fields : PreEq (origin ctx raw) before.host
  memory : before.mem = preparedData ctx.protocol

namespace BeforeWrite

theorem isView {ctx : Context} {raw : Storage} {before : HostStore NearState} (h : BeforeWrite ctx raw before) :
    before.host.context.isView = false := h.fields.isView

theorem issue {ctx : Context} {raw : Storage} {before : HostStore NearState} (h : BeforeWrite ctx raw before) :
    before.host.lastExecutionIssue = none := h.fields.issue

theorem input {ctx : Context} {raw : Storage} {before : HostStore NearState} (h : BeforeWrite ctx raw before) :
    before.host.context.input = ctx.args := h.fields.input

theorem represents {ctx : Context} {raw : Storage} {before : HostStore NearState} (h : BeforeWrite ctx raw before) :
    StorageOverlay.Represents before.host ctx raw := by
  refine ⟨h.fields.current, ?_⟩
  intro key
  rw [h.fields.storage]
  rfl

theorem paid {ctx : Context} {raw : Storage} {before : HostStore NearState} (h : BeforeWrite ctx raw before)
    (charges : List Charge) (hburn : ∀ c ∈ charges, BurnsOnly c) :
    BeforeWrite ctx raw (Output.paidStore before (applyCharges before.host charges).1) :=
  ⟨h.fields.trans (PreEq.paid before charges hburn), h.memory⟩

theorem input_return {ctx : Context} {raw : Storage} {before after : HostStore NearState}
    (h : BeforeWrite ctx raw before) (extra : Nat) (values : List Value)
    (hreturn : (metered extra "input" inputFn).invoke before [.i64 0] = .Return values after) :
    BeforeWrite ctx raw after ∧ after.host.registers 0 = some ctx.args := by
  obtain ⟨hm, hf, hr⟩ := input_return_frame extra before after values hreturn
  exact ⟨⟨h.fields.trans hf, hm.trans h.memory⟩, hr.trans (congrArg some h.input)⟩

end BeforeWrite

private theorem prepared_key (ctx : Context) (raw : Storage) (before : HostStore NearState)
    (hm : before.mem = preparedData ctx.protocol) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg before 0 1 = some "k".toUTF8.toList := by
  let reference := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  have hmem : before.mem = reference.mem := hm.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw).symm
  calc
    getMemOrReg before 0 1 = getMemOrReg reference 0 1 := by
      simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte, hmem]
    _ = some "k".toUTF8.toList := emptyPaid_key ctx raw hpages

/-- Actual primitive readiness follows from the original empty-base WF and
functional frame. The original proof observer, not a post-run result, supplies
the explicit final recorded-proof acceptance obligation. -/
theorem empty_freshReady (ctx : Context) (raw : Storage) (before : HostStore NearState)
    (h : BeforeWrite ctx raw before) (hregister : before.host.registers 0 = some ctx.args)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    StorageMeteredBudget.FreshReady before 1 0 u64Max 0 := by
  have hcurrent : before.host.context.currentAccountId = ctx.current.bytes := h.fields.current
  have haccount : before.host.storageAccounting = some ctx.trie := h.fields.accounting
  have hcfg := h.fields.config
  refine ⟨"k".toUTF8.toList, ctx.args, ctx.trie, ctx.trie, haccount,
    prepared_key ctx raw before h.memory hpages, ?_, ?_, ?_, ?_, ?_⟩
  · intro limit hl
    rw [hcfg] at hl
    change some ctx.protocol.wasm.limits.maxLengthStorageKey = some limit at hl
    cases Option.some.inj hl
    simpa only [show "k".toUTF8.toList.length = 1 by decide +kernel] using hkey
  · rw [hcurrent]
    exact Near.TrieOverlay.getReference_empty_unselected ctx.trie _ true
      (Near.TrieOverlay.base_empty_of_canonical ctx.trie hentries hwf.trie_canonical) hselected
  · exact StorageEmpty.storage_none before ctx raw.toFinset hwf raw rfl h.represents _ hentries hselected
  · simp only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero, hregister]
  · rw [hcurrent]
    simpa only [recordedStorageError, h.fields.config, h.fields.proof] using hproof

/-- The Wasm view at storage entry still carries the original prepared memory
and pre-write functional data, despite arbitrary internal budget enlargement. -/
structure StoreBeforeWrite (ctx : Context) (raw : Storage) (store : Store NearState) : Prop where
  fields : PreEq (origin ctx raw) store.host
  memory : store.memOf moduleInstance = some (preparedData ctx.protocol)

namespace StoreBeforeWrite

theorem charged {ctx : Context} {raw : Storage} {store : Store NearState}
    (h : StoreBeforeWrite ctx raw store) (cost : Nat) : StoreBeforeWrite ctx raw (chargedStore store cost) :=
  ⟨h.fields.trans (PreEq.charged store.host cost), h.memory⟩

theorem hostView {ctx : Context} {raw : Storage} {store : Store NearState}
    (h : StoreBeforeWrite ctx raw store) : BeforeWrite ctx raw (MeteredHostBudget.hostView store moduleInstance) := by
  exact ⟨h.fields, by simp only [MeteredHostBudget.hostView, h.memory, Option.getD_some]⟩

end StoreBeforeWrite

/-- A constructed auxiliary high initial body keeps all functional resources. -/
theorem initial_beforeWrite (ctx : Context) (raw : Storage) (budget : Nat) :
    StoreBeforeWrite ctx raw
      (initializedStore ctx.protocol (enlargeHost (origin ctx raw) budget) (preparedData ctx.protocol)) :=
  ⟨PreEq.enlarged _ _, rfl⟩

/-- The exact phase-7 readiness premise of concrete machine replay is derived
from original WF, prepared memory, input register and the shared proof check. -/
theorem storageReady_of_original (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (hregister : store.host.registers 0 = some ctx.args)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    StorageReady ctx.protocol store := by
  let before := MeteredHostBudget.hostView (chargedStore store ctx.protocol.wasm.regularOpCost) moduleInstance
  have hb : BeforeWrite ctx raw before := (h.charged ctx.protocol.wasm.regularOpCost).hostView
  have hp := hb.paid _ (StorageBudget.plan_burnsOnly before 1 0 u64Max 0)
  have hr : (StorageMeteredBudget.paid before 1 0 u64Max 0).host.registers 0 = some ctx.args := by
    have hf := congrArg (fun host : NearState => host.registers 0)
      (applyCharges_frame before.host _ (StorageBudget.plan_burnsOnly before 1 0 u64Max 0))
    exact hf.trans hregister
  intro _
  exact Or.inl (empty_freshReady ctx raw _ hp hr hwf hpages hkey hentries hselected hproof)

/-- Pure constants/drop preserve the complete pre-write frame and input
register, on successful transitions and on stopped charge-failure prefixes. -/
theorem pure_frame (cfg : WasmConfig) (op : PureOp) (store : Store NearState) (limits : ExecLimits)
    (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : List Instr) :
    let next := (advance cfg (.next (atCode store limits stack frame callers (op.instr :: code)))).1
    PreEq store.host next.host ∧ next.store.memOf moduleInstance = store.memOf moduleInstance ∧
      next.host.registers = store.host.registers := by
  rw [advance_pure]
  cases he : (chargeHost store.host cfg.regularOpCost).2 <;> exact ⟨rfl, rfl, rfl⟩

/-- Committing a host return preserves the caller's prepared memory. -/
theorem commit_memory (store : Store NearState) (host : NearState) (mem : Memory)
    (hm : store.memOf moduleInstance = some mem) :
    (Exec.commitHost store (some moduleInstance) host (some mem)).memOf moduleInstance = some mem := by
  have hget : store.mems[0]? = some mem := hm
  have hb := (Array.getElem?_eq_some_iff.mp hget).1
  simp only [Exec.commitHost, Store.memOf, Store.setMemOf, moduleInstance, Array.getElem?_singleton, ↓reduceIte, Option.bind_some]
  simpa only [Array.set!_eq_setIfInBounds] using
    (Array.getElem?_setIfInBounds_self_of_lt (a := mem) hb)

/-- A real returned input call can be committed without an abstract frame
callback: it establishes all pre-write resources and the input register. -/
theorem input_commit_beforeWrite (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (extra : Nat)
    (values : List Value) (after : HostStore NearState)
    (hr : (metered extra "input" inputFn).invoke (MeteredHostBudget.hostView store moduleInstance) [.i64 0] =
      .Return values after) :
    StoreBeforeWrite ctx raw (Exec.commitHost store (some moduleInstance) after.host (some after.mem)) ∧
      after.host.registers 0 = some ctx.args := by
  obtain ⟨hf, hg⟩ := h.hostView.input_return extra values hr
  refine ⟨⟨hf.fields, ?_⟩, hg⟩
  rw [hf.memory]
  exact commit_memory store after.host _ h.memory

/-- Continuing pure instructions preserve the original pre-write store frame. -/
theorem pure_beforeWrite (ctx : Context) (raw : Storage) (op : PureOp) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (limits : ExecLimits) (stack : Array Value)
    (code : List Instr) :
    StoreBeforeWrite ctx raw
      (advance ctx.protocol.wasm (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1.store := by
  obtain ⟨hf, hm, _⟩ := pure_frame ctx.protocol.wasm op store limits stack saveFrame [] code
  have hh : (advance ctx.protocol.wasm (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1.host =
      (advance ctx.protocol.wasm (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1.store.host := by
    cases (advance ctx.protocol.wasm (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1 <;> rfl
  rw [hh] at hf
  exact ⟨h.fields.trans hf, hm.trans h.memory⟩

/-- An actual continuing input transition establishes register zero and the
original pre-write frame, including the memory committed by the interpreter. -/
theorem advance_input_beforeWrite (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (hi : Installed ctx.protocol store)
    (limits : ExecLimits) (next : Config NearState)
    (he : (advance ctx.protocol.wasm (phaseMachine store limits 1 0)).2 = none)
    (hn : (advance ctx.protocol.wasm (phaseMachine store limits 1 0)).1 = .next next) :
    StoreBeforeWrite ctx raw next.store ∧ next.store.host.registers 0 = some ctx.args := by
  have ha := advance_host ctx.protocol.wasm store moduleInstance limits [] [.i64 0] saveFrame []
    (phaseCode 2) 0 0 (metered ctx.protocol.fees.numExtraBytesRecord "input" inputFn)
    hi.module rfl hi.input rfl
  simp only [List.nil_append] at ha
  change advance ctx.protocol.wasm (phaseMachine store limits 1 0) = _ at ha
  rw [ha] at he hn
  cases hc : (chargeHost store.host ctx.protocol.wasm.regularOpCost).2 with
  | some error => simp [hc] at he
  | none =>
    simp only [hc] at he hn
    cases hr : (metered ctx.protocol.fees.numExtraBytesRecord "input" inputFn).invoke
      (MeteredHostBudget.hostView (chargedStore store ctx.protocol.wasm.regularOpCost) moduleInstance) [.i64 0] with
    | Trap after message => simp [hr, callResult, chargeWasm] at hn
    | Return values after =>
      have hf := input_commit_beforeWrite ctx raw (chargedStore store ctx.protocol.wasm.regularOpCost)
        (h.charged _) ctx.protocol.fees.numExtraBytesRecord values after hr
      simp only [hr, callResult, chargeWasm] at hn
      cases hn
      exact ⟨⟨hf.1.fields.trans (PreEq.charged _ 0), hf.1.memory⟩, hf.2⟩

private theorem pure_next_beforeWrite (ctx : Context) (raw : Storage) (op : PureOp) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (limits : ExecLimits) (stack : Array Value)
    (code : List Instr) (next : Config NearState)
    (hn : (advance ctx.protocol.wasm (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1 = .next next) :
    StoreBeforeWrite ctx raw next.store ∧ next.store.host.registers = store.host.registers := by
  have hf := pure_beforeWrite ctx raw op store h limits stack code
  have hr := (pure_frame ctx.protocol.wasm op store limits stack saveFrame [] code).2.2
  rw [hn] at hf hr
  exact ⟨hf, hr⟩

/-- All actual continuing pre-write phases preserve the original functional
frame. Crossing input initializes register zero; later constants preserve it.
The hypotheses concern only the source resources and actual one-step exit. -/
theorem prewrite_next (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (hi : Installed ctx.protocol store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (next : Config NearState)
    (hpc : pc.val < 7) (hregister : 2 ≤ pc.val → store.host.registers 0 = some ctx.args)
    (he : (advance ctx.protocol.wasm (phaseMachine store limits pc.val written)).2 = none)
    (hn : (advance ctx.protocol.wasm (phaseMachine store limits pc.val written)).1 = .next next) :
    StoreBeforeWrite ctx raw next.store ∧
      (2 ≤ pc.val + 1 → next.store.host.registers 0 = some ctx.args) := by
  fin_cases pc
  · obtain ⟨hf, _⟩ := pure_next_beforeWrite ctx raw (.i64const 0) store h limits _ _ next hn
    exact ⟨hf, by intro hx; change 2 ≤ 1 at hx; omega⟩
  · obtain ⟨hf, hr⟩ := advance_input_beforeWrite ctx raw store h hi limits next he hn
    exact ⟨hf, fun _ => hr⟩
  · obtain ⟨hf, hr⟩ := pure_next_beforeWrite ctx raw (.i64const 1) store h limits _ _ next hn
    exact ⟨hf, fun _ => (congrArg (fun regs => regs 0) hr).trans (hregister (by decide))⟩
  · obtain ⟨hf, hr⟩ := pure_next_beforeWrite ctx raw (.i64const 0) store h limits _ _ next hn
    exact ⟨hf, fun _ => (congrArg (fun regs => regs 0) hr).trans (hregister (by decide))⟩
  · obtain ⟨hf, hr⟩ := pure_next_beforeWrite ctx raw (.i64const u64Max) store h limits _ _ next hn
    exact ⟨hf, fun _ => (congrArg (fun regs => regs 0) hr).trans (hregister (by decide))⟩
  · obtain ⟨hf, hr⟩ := pure_next_beforeWrite ctx raw (.i64const 0) store h limits _ _ next hn
    exact ⟨hf, fun _ => (congrArg (fun regs => regs 0) hr).trans (hregister (by decide))⟩
  · obtain ⟨hf, hr⟩ := pure_next_beforeWrite ctx raw (.i64const u64Max) store h limits _ _ next hn
    exact ⟨hf, fun _ => (congrArg (fun regs => regs 0) hr).trans (hregister (by decide))⟩
  all_goals norm_num at hpc

/-- The next exact source phase and its original resources are established
together; this is the closed pre-write prefix needed to reach storage. -/
theorem prewrite_phase_next (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (hi : Installed ctx.protocol store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (next : Config NearState)
    (hpc : pc.val < 7) (hregister : 2 ≤ pc.val → store.host.registers 0 = some ctx.args)
    (he : (advance ctx.protocol.wasm (phaseMachine store limits pc.val written)).2 = none)
    (hn : (advance ctx.protocol.wasm (phaseMachine store limits pc.val written)).1 = .next next) :
    ∃ (index : Fin 16) (flag : UInt64) (after : Store NearState), index.val = pc.val + 1 ∧
      next = atCode after limits (phaseStack index.val flag) saveFrame [] (phaseCode index.val) ∧
      Installed ctx.protocol after ∧ StoreBeforeWrite ctx raw after ∧
      (2 ≤ index.val → after.host.registers 0 = some ctx.args) := by
  obtain ⟨index, flag, after, hp, hn', hi'⟩ := Progress.phase_next ctx.protocol store hi limits pc written next he hn
  obtain ⟨hf, hr⟩ := prewrite_next ctx raw store h hi limits pc written next hpc hregister he hn
  rw [hn'] at hf hr
  change 2 ≤ pc.val + 1 → after.host.registers 0 = some ctx.args at hr
  exact ⟨index, flag, after, hp, hn', hi', hf, by simpa only [hp] using hr⟩

/-- Output operations preserve view mode on every actual host exit. -/
theorem output_isView (op : MeteredOutputBudget.OutputOp) (extra : Nat)
    (before : HostStore NearState) (len ptr : UInt64) :
    (Budget.resultStore ((op.fn extra).invoke before [.i64 len, .i64 ptr])).host.context.isView =
      before.host.context.isView := by
  have hburn : ∀ c ∈ chargesBefore op.name before [.i64 len, .i64 ptr], BurnsOnly c := by
    cases op
    · exact Output.logUtf8_burnsOnly before len ptr
    · exact Output.valueReturn_burnsOnly before len ptr
  have hp := (PreEq.paid before _ hburn).isView
  have hraw (st : HostStore NearState) :
      (Budget.resultStore (op.raw.invoke st [.i64 len, .i64 ptr])).host.context.isView = st.host.context.isView := by
    cases op with
    | logUtf8 =>
      cases hr : (logUtf8Read st len ptr).result with
      | ok msg => rw [show MeteredOutputBudget.OutputOp.logUtf8.raw = logUtf8Fn from rfl, Output.logUtf8_ok st len ptr msg hr]; rfl
      | error error => rw [show MeteredOutputBudget.OutputOp.logUtf8.raw = logUtf8Fn from rfl, Output.logUtf8_error st len ptr error hr]; rfl
    | valueReturn =>
      dsimp only [MeteredOutputBudget.OutputOp.raw, valueReturnFn, checkDataLimit]
      repeat' (first | rfl | split)
  cases op with
  | logUtf8 =>
    rw [show MeteredOutputBudget.OutputOp.logUtf8.fn extra = metered extra "log_utf8" logUtf8Fn from rfl,
      Output.metered_logUtf8_eq]
    cases hc : applyCharges before.host (chargesBefore "log_utf8" before [.i64 len, .i64 ptr]) with
    | mk paid error =>
      change (Output.paidStore before (applyCharges before.host
        (chargesBefore "log_utf8" before [.i64 len, .i64 ptr])).1).host.context.isView = _ at hp
      rw [hc] at hp
      cases error with
      | some error => exact hp
      | none => exact (hraw (Output.paidStore before paid)).trans hp
  | valueReturn =>
    rw [show MeteredOutputBudget.OutputOp.valueReturn.fn extra = metered extra "value_return" valueReturnFn from rfl,
      Output.metered_valueReturn_eq]
    cases hc : applyCharges before.host (chargesBefore "value_return" before [.i64 len, .i64 ptr]) with
    | mk paid error =>
      change (Output.paidStore before (applyCharges before.host
        (chargesBefore "value_return" before [.i64 len, .i64 ptr])).1).host.context.isView = _ at hp
      rw [hc] at hp
      cases error with
      | some error => exact hp
      | none =>
        cases he : preInvokeError "value_return" (Output.paidStore before paid) [.i64 len, .i64 ptr] with
        | some error => simpa only [he, Budget.resultStore, trapWith] using hp
        | none => simpa only [he, MeteredOutputBudget.OutputOp.raw] using (hraw (Output.paidStore before paid)).trans hp

private theorem call_next_view (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (index addr : Nat) (fn : NearHostFn NearState)
    (input : List Value) (code : List Instr) (next : Config NearState)
    (haddr : moduleInstance.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : input.length = fn.params.length)
    (hv : ∀ values after, fn.invoke
      (MeteredHostBudget.hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) input =
      .Return values after → after.host.context.isView = store.host.context.isView)
    (he : (advance cfg.wasm (.next (atCode store limits input.toArray saveFrame [] (.call index :: code)))).2 = none)
    (hn : (advance cfg.wasm (.next (atCode store limits input.toArray saveFrame [] (.call index :: code)))).1 = .next next) :
    next.store.host.context.isView = store.host.context.isView := by
  have ha := advance_host cfg.wasm store moduleInstance limits [] input saveFrame [] code
    index addr fn hi.module haddr hfn hargs
  simp only [List.nil_append] at ha
  rw [ha] at he hn
  cases hc : (chargeHost store.host cfg.wasm.regularOpCost).2 with
  | some error => simp [hc] at he
  | none =>
    simp only [hc] at hn
    cases hr : fn.invoke
      (MeteredHostBudget.hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) input with
    | Trap after message => simp [hr, callResult, chargeWasm] at hn
    | Return values after =>
      have hview := hv values after hr
      simp only [hr, callResult, chargeWasm] at hn
      cases hn
      exact hview

private theorem pure_next_view (cfg : WasmConfig) (op : PureOp) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (code : List Instr) (next : Config NearState)
    (hn : (advance cfg (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1 = .next next) :
    next.store.host.context.isView = store.host.context.isView := by
  have hf := (pure_frame cfg op store limits stack saveFrame [] code).1.isView
  rw [hn] at hf
  exact hf

/-- Every actual continuing phase preserves the structured issue. Trie errors
may still terminate in a trap; no assertion about those trap markers is made. -/
theorem phase_next_issue (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (next : Config NearState)
    (hview : store.host.context.isView = false)
    (hn : (advance cfg.wasm (phaseMachine store limits pc.val written)).1 = .next next) :
    next.store.host.lastExecutionIssue = store.host.lastExecutionIssue := by
  have hpure (op : PureOp) (stack : Array Value) (code : List Instr)
      (hn : (advance cfg.wasm (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1 = .next next) :
      next.store.host.lastExecutionIssue = store.host.lastExecutionIssue := by
    have hf := (pure_frame cfg.wasm op store limits stack saveFrame [] code).1.issue
    rw [hn] at hf
    exact hf
  fin_cases pc
  · exact hpure (.i64const 0) _ _ hn
  · have hf := advance_input_issue cfg.wasm cfg.fees.numExtraBytesRecord store moduleInstance limits [] saveFrame [] (phaseCode 2) 0 0 0 hi.module rfl hi.input
    rw [show (advance cfg.wasm (.next (atCode store limits (([] : List Value) ++ [Value.i64 0]).toArray saveFrame [] (.call 0 :: phaseCode 2)))).1 = .next next from hn] at hf
    exact hf
  · exact hpure (.i64const 1) _ _ hn
  · exact hpure (.i64const 0) _ _ hn
  · exact hpure (.i64const u64Max) _ _ hn
  · exact hpure (.i64const 0) _ _ hn
  · exact hpure (.i64const u64Max) _ _ hn
  · exact MeteredStorageBudget.advance_next_issue cfg.wasm cfg.fees.numExtraBytesRecord store moduleInstance limits [] saveFrame [] (phaseCode 8) 1 1 1 0 u64Max 0 hi.module rfl hi.storage hview next hn
  · exact hpure .drop _ _ hn
  · exact hpure (.i64const 5) _ _ hn
  · exact hpure (.i64const 1) _ _ hn
  · have hf := MeteredOutputBudget.advance_issue .logUtf8 cfg.wasm cfg.fees.numExtraBytesRecord store moduleInstance limits [] saveFrame [] (phaseCode 12) 2 2 5 1 hi.module rfl hi.log
    rw [show (advance cfg.wasm (.next (atCode store limits (([] : List Value) ++ [Value.i64 5, Value.i64 1]).toArray saveFrame [] (.call 2 :: phaseCode 12)))).1 = .next next from hn] at hf
    exact hf
  · exact hpure (.i64const u64Max) _ _ hn
  · exact hpure (.i64const 0) _ _ hn
  · have hf := MeteredOutputBudget.advance_issue .valueReturn cfg.wasm cfg.fees.numExtraBytesRecord store moduleInstance limits [] saveFrame [] (phaseCode 15) 3 3 u64Max 0 hi.module rfl hi.returned
    rw [show (advance cfg.wasm (.next (atCode store limits (([] : List Value) ++ [Value.i64 u64Max, Value.i64 0]).toArray saveFrame [] (.call 3 :: phaseCode 15)))).1 = .next next from hn] at hf
    exact hf
  · change (advance cfg.wasm (.next (atCode store limits #[] saveFrame [] []))).1 = .next next at hn
    simp only [advance, show nextInstructionGas cfg.wasm (atCode store limits #[] saveFrame [] []) = 0 from rfl] at hn
    cases he : (chargeHost store.host 0).2 with
    | some error => simp only [chargeConfig, atCode, he] at hn; cases hn; rfl
    | none => simp [chargeConfig, he, Exec.step, Exec.leave, atCode, saveFrame, chargeWasm] at hn

/-- Nonview execution is preserved across every actual continuing phase. -/
theorem phase_next_view (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (next : Config NearState)
    (he : (advance cfg.wasm (phaseMachine store limits pc.val written)).2 = none)
    (hn : (advance cfg.wasm (phaseMachine store limits pc.val written)).1 = .next next) :
    next.store.host.context.isView = store.host.context.isView := by
  fin_cases pc
  · exact pure_next_view cfg.wasm (.i64const 0) store limits _ _ next hn
  · apply call_next_view cfg store hi limits 0 0 (metered cfg.fees.numExtraBytesRecord "input" inputFn) [.i64 0] (phaseCode 2) next rfl hi.input rfl _ he hn
    intro values after hr
    exact (input_return_frame _ _ _ _ hr).2.1.isView
  · exact pure_next_view cfg.wasm (.i64const 1) store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const 0) store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const u64Max) store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const 0) store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const u64Max) store limits _ _ next hn
  · apply call_next_view cfg store hi limits 1 1 (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) (StorageMetered.args 1 0 u64Max 0) (phaseCode 8) next rfl hi.storage rfl _ he hn
    intro values after hr
    exact (StorageReturnFrame.metered_return_frame _ _ _ 1 0 u64Max 0 values hr).isView
  · exact pure_next_view cfg.wasm .drop store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const 5) store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const 1) store limits _ _ next hn
  · apply call_next_view cfg store hi limits 2 2 (MeteredOutputBudget.OutputOp.logUtf8.fn cfg.fees.numExtraBytesRecord) [.i64 5, .i64 1] (phaseCode 12) next rfl hi.log rfl _ he hn
    intro values after hr
    have hv := output_isView .logUtf8 cfg.fees.numExtraBytesRecord (MeteredHostBudget.hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) 5 1
    rw [hr] at hv
    exact hv
  · exact pure_next_view cfg.wasm (.i64const u64Max) store limits _ _ next hn
  · exact pure_next_view cfg.wasm (.i64const 0) store limits _ _ next hn
  · apply call_next_view cfg store hi limits 3 3 (MeteredOutputBudget.OutputOp.valueReturn.fn cfg.fees.numExtraBytesRecord) [.i64 u64Max, .i64 0] (phaseCode 15) next rfl hi.returned rfl _ he hn
    intro values after hr
    have hv := output_isView .valueReturn cfg.fees.numExtraBytesRecord (MeteredHostBudget.hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) u64Max 0
    rw [hr] at hv
    exact hv
  · change (advance cfg.wasm (.next (atCode store limits #[] saveFrame [] []))).1 = .next next at hn
    simp only [advance, show nextInstructionGas cfg.wasm (atCode store limits #[] saveFrame [] []) = 0 from rfl] at hn
    cases hc : (chargeHost store.host 0).2 with
    | some error => simp only [chargeConfig, atCode, hc] at hn; cases hn; rfl
    | none => simp [chargeConfig, hc, Exec.step, Exec.leave, atCode, saveFrame, chargeWasm] at hn

/-- Functional resources required at an actual code suffix. The original trie
frame is retained only until storage; subsequent host replay uses StoreBelow. -/
structure Resources (ctx : Context) (raw : Storage) (pc : Nat) (store : Store NearState) : Prop where
  nonview : store.host.context.isView = false
  fresh : store.host.lastExecutionIssue = none
  beforeWrite : pc ≤ 7 → StoreBeforeWrite ctx raw store
  register : 2 ≤ pc → pc ≤ 7 → store.host.registers 0 = some ctx.args

/-- The functional invariant tracks the same actual installed code shape. -/
def Functional (ctx : Context) (raw : Storage) (limits : ExecLimits) : Machine → Prop
  | .next c => ∃ (pc : Fin 16) (written : UInt64) (store : Store NearState),
      c = atCode store limits (phaseStack pc.val written) saveFrame [] (phaseCode pc.val) ∧
      Installed ctx.protocol store ∧ Resources ctx raw pc.val store
  | .done _ _ | .trap _ _ => True

theorem initial_resources (ctx : Context) (raw : Storage) (budget : Nat) :
    Resources ctx raw 0
      (initializedStore ctx.protocol (enlargeHost (origin ctx raw) budget) (preparedData ctx.protocol)) := by
  exact ⟨rfl, rfl, fun _ => initial_beforeWrite ctx raw budget, by intro h; omega⟩

/-- All error-free actual continuing transitions close the functional invariant.
No host execution contract or whole-run result occurs among its hypotheses. -/
theorem functional_continue (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (machine : Machine) (h : Functional ctx raw limits machine)
    (he : (advance ctx.protocol.wasm machine).2 = none) :
    Functional ctx raw limits (advance ctx.protocol.wasm machine).1 := by
  cases machine with
  | done values store => trivial
  | trap reason store => trivial
  | next c =>
    obtain ⟨pc, written, store, rfl, hi, hr⟩ := h
    change Functional ctx raw limits (advance ctx.protocol.wasm (phaseMachine store limits pc.val written)).1
    cases hn : (advance ctx.protocol.wasm (phaseMachine store limits pc.val written)).1 with
    | done values after => trivial
    | trap reason after => trivial
    | next next =>
      obtain ⟨index, flag, after, hp, hf, hi'⟩ := Progress.phase_next ctx.protocol store hi limits pc written next he hn
      refine ⟨index, flag, after, hf, hi', ?_⟩
      have hv := phase_next_view ctx.protocol store hi limits pc written next he hn
      have hs := phase_next_issue ctx.protocol store hi limits pc written next hr.nonview hn
      rw [hf] at hv hs
      refine ⟨hv.trans hr.nonview, hs.trans hr.fresh, ?_, ?_⟩
      · intro hindex
        have hpc : pc.val < 7 := by omega
        have hb := prewrite_next ctx raw store (hr.beforeWrite (by omega)) hi limits pc written next
          hpc (fun hpc' => hr.register hpc' (by omega)) he hn
        rw [hf] at hb
        exact hb.1
      · intro hindex hindex'
        have hpc : pc.val < 7 := by omega
        have hb := prewrite_next ctx raw store (hr.beforeWrite (by omega)) hi limits pc written next
          hpc (fun hpc' => hr.register hpc' (by omega)) he hn
        rw [hf] at hb
        exact hb.2 (by omega)

/-- Actual argument validation rejects a zero key bound before trie work. -/
theorem preInvoke_key_bound (before : HostStore NearState)
    (hk : getMemOrReg before 0 1 = some "k".toUTF8.toList)
    (hpre : preInvokeError "storage_write" before (StorageMetered.args 1 0 u64Max 0) = none) :
    ∀ limit, before.host.config.maxStorageKeyLen = some limit → 1 ≤ limit := by
  intro limit hlimit
  by_contra hn
  have hlength : limit < "k".toUTF8.toList.length := by
    rw [show "k".toUTF8.toList.length = 1 by decide +kernel]
    omega
  have hlength' : limit < "k".toByteArray.toList.length := hlength
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, StorageMetered.args,
    argU64, hk, hlimit, hlength'] at hpre

/-- Even when the original key limit rejects this method, the replay premise
needs readiness only after the actual validator accepts. Thus no key-limit
acceptance assumption is required at the outer simulation interface. -/
theorem storageReady_allKeyLimits (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (hregister : store.host.registers 0 = some ctx.args)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    StorageReady ctx.protocol store := by
  let before := MeteredHostBudget.hostView (chargedStore store ctx.protocol.wasm.regularOpCost) moduleInstance
  have hb : BeforeWrite ctx raw before := (h.charged ctx.protocol.wasm.regularOpCost).hostView
  have hp := hb.paid _ (StorageBudget.plan_burnsOnly before 1 0 u64Max 0)
  have hr : (StorageMeteredBudget.paid before 1 0 u64Max 0).host.registers 0 = some ctx.args := by
    have hf := congrArg (fun host : NearState => host.registers 0)
      (applyCharges_frame before.host _ (StorageBudget.plan_burnsOnly before 1 0 u64Max 0))
    exact hf.trans hregister
  intro hpre
  have hcfg : (StorageMeteredBudget.paid before 1 0 u64Max 0).host.config.maxStorageKeyLen =
      some ctx.protocol.wasm.limits.maxLengthStorageKey := congrArg NearConfig.maxStorageKeyLen hp.fields.config
  have hkey := preInvoke_key_bound _ (prepared_key ctx raw _ hp.memory hpages) hpre _ hcfg
  exact Or.inl (empty_freshReady ctx raw _ hp hr hwf hpages hkey hentries hselected hproof)

/-- The simulation carries a low-side reachable functional invariant; the
machine relation already fixes every functional resource across budgets. -/
def SimulationRelation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (small large : Machine) : Prop :=
  MachineBelow small large ∧ Functional ctx raw limits small

/-- Concrete whole-body one-step simulation. Its storage readiness is derived
from original empty-base WF, not from a host replay or execution premise. -/
theorem stepSimulation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    StepSimulation ctx.protocol.wasm (SimulationRelation ctx raw limits) := by
  intro small large hrel
  have hfunctional := hrel.state.2
  have hstep : MatchesOrGas MachineBelow (advance ctx.protocol.wasm small) (advance ctx.protocol.wasm large) := by
    cases hbelow : hrel.state.1 with
    | @next small large hc =>
      obtain ⟨pc, written, store, hs, hi, hr⟩ := hfunctional
      subst small
      have hlarge : large = atCode large.store limits (phaseStack pc.val written) saveFrame [] (phaseCode pc.val) := by
        cases large
        obtain ⟨hstore, hthread, hlimits⟩ := hc
        simp only [atCode] at hthread hlimits
        cases hthread
        cases hlimits
        rfl
      rw [hlarge]
      exact phase_advance_replay ctx.protocol hc.store hi limits pc written hr.nonview hr.fresh (by
        intro hp
        exact storageReady_allKeyLimits ctx raw store (hr.beforeWrite (by omega))
          (hr.register (by omega) (by omega)) hwf hpages hentries hselected hproof)
    | done values hs => exact Or.inl ⟨(MachineBelow.done values hs).related, rfl⟩
    | trapped reason hs => exact Or.inl ⟨(MachineBelow.trapped reason hs).related, rfl⟩
  rcases hstep with ⟨hmatched, herror⟩ | hgas
  · by_cases he : (advance ctx.protocol.wasm small).2 = none
    · left
      have hclosed := functional_continue ctx raw limits small hfunctional he
      exact ⟨⟨⟨hmatched.state, hclosed⟩, hmatched.control, hmatched.context, hmatched.logs, hmatched.gas⟩, herror⟩
    · right
      refine ⟨Progress.advance_error_gas ctx.protocol.wasm small he, ?_⟩
      change List.IsPrefix _ _
      rw [hmatched.logs]
  · exact Or.inr hgas

/-- The functional low shape transports to its functionally identical high
machine, including the actual installed module and four host slots. -/
theorem related_shape (ctx : Context) (raw : Storage) (limits : ExecLimits)
    {small large : Machine} (h : Related (SimulationRelation ctx raw limits) small large) :
    Shape ctx.protocol limits large := by
  have hf := h.state.2
  cases h.state.1 with
  | @next small large hc =>
    obtain ⟨pc, written, store, hs, hi, _⟩ := hf
    subst small
    have hm := congrArg Store.modules hc.store.fields
    have hfn := congrArg Store.funcs hc.store.fields
    have hi' : Installed ctx.protocol large.store := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← hm]; exact hi.module
      · rw [← hfn]; exact hi.input
      · rw [← hfn]; exact hi.storage
      · rw [← hfn]; exact hi.log
      · rw [← hfn]; exact hi.returned
    refine ⟨pc, written, large.store, ?_, hi'⟩
    cases large
    obtain ⟨hstore, hthread, hlimits⟩ := hc
    simp only [atCode] at hthread hlimits
    cases hthread
    cases hlimits
    rfl
  | done values hs => trivial
  | trapped reason hs => trivial

/-- Whole actual body runs either match or the low run aborts for protocol gas
with a log prefix. Sufficient structural fuel excludes fuel errors regardless
of host validation, trie errors or the amount of either internal gas budget. -/
theorem runSimulation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none)
    (fuel : Nat) (small large : Machine)
    (hrel : Related (SimulationRelation ctx raw limits) small large)
    (hbound : Progress.rank large ≤ fuel) :
    MatchesOrGas (SimulationRelation ctx raw limits)
        (runMetered ctx.protocol.wasm fuel small) (runMetered ctx.protocol.wasm fuel large) ∧
      (runMetered ctx.protocol.wasm fuel small).2 ≠ some (.executionIssue .fuelExhausted) := by
  have hshape := related_shape ctx raw limits hrel
  exact run_simulation_no_fuel ctx.protocol.wasm (SimulationRelation ctx raw limits)
    (stepSimulation ctx raw limits hwf hpages hentries hselected hproof)
    (Shape ctx.protocol limits) (shape_advanceInvariant ctx.protocol limits) (shape_logsMonotone ctx.protocol limits)
    fuel small large hrel hshape (Progress.run_not_fuel ctx.protocol limits fuel large hshape hbound)

/-- Initialize the common body with the original host and an internally enlarged
reference budget, retaining the original guest-visible VMContext verbatim. -/
theorem initial_related (ctx : Context) (raw : Storage) (limits : ExecLimits) (budget : Nat) :
    Related (SimulationRelation ctx raw limits)
      (phaseMachine (initializedStore ctx.protocol (origin ctx raw) (preparedData ctx.protocol)) limits 0 0)
      (phaseMachine (initializedStore ctx.protocol (enlargeHost (origin ctx raw) budget) (preparedData ctx.protocol)) limits 0 0) := by
  have hb : MachineBelow
      (phaseMachine (initializedStore ctx.protocol (origin ctx raw) (preparedData ctx.protocol)) limits 0 0)
      (phaseMachine (initializedStore ctx.protocol (enlargeHost (origin ctx raw) budget) (preparedData ctx.protocol)) limits 0 0) :=
    .next ⟨initialized_below ctx.protocol (origin ctx raw) (preparedData ctx.protocol) budget, rfl, rfl⟩
  have hr := hb.related
  refine ⟨⟨hb, ?_⟩, hr.control, hr.context, hr.logs, hr.gas⟩
  refine ⟨⟨0, by decide⟩, 0, _, rfl, initialized_installed _ _ _, ?_⟩
  exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩, by intro h; change 2 ≤ 0 at h; omega⟩

/-- The complete initialized body has budget replay with sixteen steps of
structural fuel; reference gas is arbitrary and does not alter VMContext. -/
theorem initialized_runSimulation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none)
    (budget fuel : Nat) (hfuel : 16 ≤ fuel) :
    let small := phaseMachine (initializedStore ctx.protocol (origin ctx raw) (preparedData ctx.protocol)) limits 0 0
    let large := phaseMachine (initializedStore ctx.protocol (enlargeHost (origin ctx raw) budget) (preparedData ctx.protocol)) limits 0 0
    MatchesOrGas (SimulationRelation ctx raw limits)
        (runMetered ctx.protocol.wasm fuel small) (runMetered ctx.protocol.wasm fuel large) ∧
      (runMetered ctx.protocol.wasm fuel small).2 ≠ some (.executionIssue .fuelExhausted) := by
  exact runSimulation ctx raw limits hwf hpages hentries hselected hproof fuel _ _
    (initial_related ctx raw limits budget) (by change 16 ≤ fuel; exact hfuel)

end WNear.Skeleton.FunctionalInvariant
