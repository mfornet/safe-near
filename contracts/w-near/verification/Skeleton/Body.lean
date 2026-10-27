import Skeleton.Prepared
import NearVM.MeteredCall

/-!
# Composing the walking method

The actual fifteen Wasm opcodes are composed from instruction and direct-call
rules. Host invocation equations and bounded host costs are explicit premises;
no premise assumes execution of the method or any multi-instruction suffix.
The initial frame is already active: contract loading and entry activation are
separate costs at the runtime boundary.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- Charge a fixed number of regular opcodes, leaving other store resources. -/
def chargedMany (store : Store NearState) (cost : Nat) : Nat → Store NearState
  | 0 => store
  | n + 1 => chargedMany (chargedStore store cost) cost n

private theorem charged_credits (store : Store NearState) (cost rest : Nat)
    (h : store.host.gas.Credits (cost + rest)) :
    (chargedStore store cost).host.gas.Credits rest :=
  (Pays.chargeWasm (.done [] store) cost rest h).2.2.2.2

/-- A repeated constant block. The walking body uses this four times, with
one, five, two and two constants respectively. -/
theorem wp_i64_consts (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (ns : List UInt64) (post : Post)
    (hcredits : store.host.gas.Credits (ns.length * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (chargedMany store cfg.regularOpCost ns.length) limits
        (base ++ ns.map Value.i64).toArray frame callers code)) rest post) :
    WP cfg (fuel + ns.length)
      (.next (atCode store limits base.toArray frame callers (ns.map Instr.i64_const ++ code)))
      (ns.length * cfg.regularOpCost + rest) post := by
  induction ns generalizing store base with
  | nil => simpa [chargedMany] using hnext
  | cons n ns ih =>
    have hc : store.host.gas.Credits
        (cfg.regularOpCost + (ns.length * cfg.regularOpCost + rest)) := by
      simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcredits
    have ht := ih (chargedStore store cfg.regularOpCost) (base ++ [.i64 n])
      (charged_credits store _ _ hc)
      (by simpa [chargedMany, List.map_cons, List.append_assoc] using hnext)
    have step := wp_i64_const cfg (fuel + ns.length) (ns.length * cfg.regularOpCost + rest)
      store limits base.toArray frame callers (ns.map Instr.i64_const ++ code) n post hc
      (by simpa using ht)
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step

/-- Discard the storage-write return flag, paying the actual drop opcode. -/
theorem wp_drop (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (value : Value) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits (stack.push value) frame callers (.drop :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push value) frame callers (.drop :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- The active zero-argument, zero-result `save` frame. -/
def saveFrame : CallFrame :=
  { locals := #[], inst := 0, arity := 0, height := 0, labels := [], code := [] }

/-- Returning from `save` is administrative and consumes no regular opcode. -/
theorem wp_finish_save (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (post : Post) (hcredits : store.host.gas.Credits rest)
    (hpost : post rest (.done [] store) none) :
    WP cfg (fuel + 1) (.next (atCode store limits #[] saveFrame [] [])) rest post := by
  let c := atCode store limits #[] saveFrame [] []
  have hzero : chargeConfig c 0 = (c, none) := by
    have hz := chargeWasm_zero (.next c) (hcredits.mono (Nat.zero_le rest))
    cases hc : chargeConfig c 0 with
    | mk c' error =>
      simp only [chargeWasm, hc] at hz
      cases hz
      rfl
  have hstep : Exec.step c = .done [] store := rfl
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  have hcost : nextInstructionGas cfg c = 0 := rfl
  rw [hcost, hzero, hstep] at h
  simp only [Nat.zero_add] at h
  apply h (by simpa only [c, atCode] using hcredits)
  · rfl
  · rfl
  · exact wp_done cfg fuel [] store rest post hcredits hpost

/-- Host invocation evidence is deliberately local to one call. It includes
actual lookup and invocation, plus the two gas bounds and unused credits. -/
structure CallEvidence (cfg : WasmConfig) (store : Store NearState) (index : Nat)
    (args results : List Value) (fn : NearHostFn NearState) (after : HostStore NearState)
    (cost rest : Nat) : Prop where
  module : store.modules[0]? = some moduleInstance
  address : moduleInstance.funcAddrs[index]? = some index
  function : store.funcs[index]? = some (.host fn.toHostFn)
  arity : args.length = fn.params.length
  invoke : fn.invoke
    ⟨(store.memOf moduleInstance).getD (Memory.new 0 none),
      (chargedStore store cfg.regularOpCost).host⟩ args = .Return results after
  burnt : after.host.gas.burnt ≤ (chargedStore store cfg.regularOpCost).host.gas.burnt + cost
  used : after.host.gas.used ≤ (chargedStore store cfg.regularOpCost).host.gas.used + cost
  credits : after.host.gas.Credits rest

/-- Instantiate the first host premise from the already proved metered
`input` contract, rather than assuming its invocation equation. -/
theorem input_evidence (cfg : RuntimeConfig) (store : Store NearState) (rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[0]? = some
      (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hlimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = true)
    (hcredits : store.host.gas.Credits (cfg.wasm.regularOpCost +
      (MeteredHosts.Input.cost store.host + rest))) :
    CallEvidence cfg.wasm store 0 [.i64 0] []
      (metered cfg.fees.numExtraBytesRecord "input" inputFn)
      (inputAfter cfg.wasm store moduleInstance 0) (MeteredHosts.Input.cost store.host) rest := by
  have hc := Pays.chargeConfig (atCode store {} #[] saveFrame [] []) cfg.wasm.regularOpCost
    (MeteredHosts.Input.cost store.host + rest) hcredits
  have hi : (inputBefore cfg.wasm store moduleInstance).host.gas.Credits
      (MeteredHosts.Input.cost (inputBefore cfg.wasm store moduleInstance).host + rest) := hc.2.2.2.2
  obtain ⟨hinvoke, _, _, hburn, hpromises, hrest⟩ :=
    MeteredHosts.Input.contract cfg.fees.numExtraBytesRecord (inputBefore cfg.wasm store moduleInstance)
      0 rest hi (by decide) hlimit
  refine ⟨hmodule, rfl, hfn, rfl, hinvoke, Nat.le_of_eq hburn, ?_, hrest⟩
  change (inputAfter cfg.wasm store moduleInstance 0).host.gas.burnt +
      (inputAfter cfg.wasm store moduleInstance 0).host.gas.promises ≤
    (chargedStore store cfg.wasm.regularOpCost).host.gas.burnt +
      (chargedStore store cfg.wasm.regularOpCost).host.gas.promises + MeteredHosts.Input.cost store.host
  change (inputAfter cfg.wasm store moduleInstance 0).host.gas.burnt =
    (chargedStore store cfg.wasm.regularOpCost).host.gas.burnt + MeteredHosts.Input.cost store.host at hburn
  change (inputAfter cfg.wasm store moduleInstance 0).host.gas.promises =
    (chargedStore store cfg.wasm.regularOpCost).host.gas.promises at hpromises
  omega

/-- Store committed by a single host call, including its opcode charge. -/
def commitCall (cfg : WasmConfig) (store : Store NearState) (after : HostStore NearState) :
    Store NearState :=
  Exec.commitHost (chargedStore store cfg.regularOpCost) (some moduleInstance)
    after.host (some after.mem)

@[simp] theorem commitCall_host (cfg : WasmConfig) (store : Store NearState)
    (after : HostStore NearState) : (commitCall cfg store after).host = after.host :=
  commitHost_host _ _ _ _

private theorem wp_evidence (cfg : WasmConfig) (fuel cost rest : Nat)
    (store : Store NearState) (limits : ExecLimits) (args results : List Value)
    (code : List Instr) (index : Nat) (fn : NearHostFn NearState) (after : HostStore NearState)
    (e : CallEvidence cfg store index args results fn after cost rest)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (cost + rest))) (post : Post)
    (hnext : WP cfg fuel
      (.next (atCode (commitCall cfg store after) limits results.toArray saveFrame [] code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits args.toArray saveFrame [] (.call index :: code)))
      (cfg.regularOpCost + (cost + rest)) post := by
  exact wp_call_host cfg fuel cost rest store limits [] args results saveFrame [] code
    index index moduleInstance fn after e.module e.address e.function e.arity hcredits
    e.invoke e.burnt e.used e.credits post hnext

private theorem chargedMany_credits (store : Store NearState) (cost rest n : Nat)
    (h : store.host.gas.Credits (n * cost + rest)) :
    (chargedMany store cost n).host.gas.Credits rest := by
  induction n generalizing store with
  | zero => simpa [chargedMany] using h
  | succ n ih =>
    apply ih
    apply charged_credits
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Separate bounds supplied by the four individual host contracts. -/
structure HostCosts where
  input : Nat
  storage : Nat
  log : Nat
  returned : Nat

namespace HostCosts

def returnBudget (c : HostCosts) (op rest : Nat) := op + (c.returned + rest)
def logSuffix (c : HostCosts) (op rest : Nat) := 2 * op + c.returnBudget op rest
def logBudget (c : HostCosts) (op rest : Nat) := op + (c.log + c.logSuffix op rest)
def storageSuffix (c : HostCosts) (op rest : Nat) := op + (2 * op + c.logBudget op rest)
def storageBudget (c : HostCosts) (op rest : Nat) := op + (c.storage + c.storageSuffix op rest)
def inputSuffix (c : HostCosts) (op rest : Nat) := 5 * op + c.storageBudget op rest
def inputBudget (c : HostCosts) (op rest : Nat) := op + (c.input + c.inputSuffix op rest)
def bodyBudget (c : HostCosts) (op rest : Nat) := op + c.inputBudget op rest

theorem bodyBudget_eq (c : HostCosts) (op rest : Nat) :
    c.bodyBudget op rest = 15 * op + c.input + c.storage + c.log + c.returned + rest := by
  simp only [bodyBudget, inputBudget, inputSuffix, storageBudget, storageSuffix,
    logBudget, logSuffix, returnBudget]
  omega

end HostCosts

/-- The four individual host results. These remain explicit until their
semantic contracts connect them to the independent storage/output model. -/
structure HostResults where
  input : HostStore NearState
  storage : HostStore NearState
  log : HostStore NearState
  returned : HostStore NearState

namespace HostResults

def beforeInput (_r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  chargedMany store cfg.regularOpCost 1
def afterInput (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  commitCall cfg (r.beforeInput cfg store) r.input
def beforeStorage (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  chargedMany (r.afterInput cfg store) cfg.regularOpCost 5
def afterStorage (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  commitCall cfg (r.beforeStorage cfg store) r.storage
def afterDrop (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  chargedStore (r.afterStorage cfg store) cfg.regularOpCost
def beforeLog (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  chargedMany (r.afterDrop cfg store) cfg.regularOpCost 2
def afterLog (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  commitCall cfg (r.beforeLog cfg store) r.log
def beforeReturn (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  chargedMany (r.afterLog cfg store) cfg.regularOpCost 2
def finalStore (r : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  commitCall cfg (r.beforeReturn cfg store) r.returned

end HostResults

@[simp] theorem chargedMany_funcs (store : Store NearState) (cost n : Nat) :
    (chargedMany store cost n).funcs = store.funcs := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => simpa [chargedMany, chargedStore] using ih (chargedStore store cost)

@[simp] theorem chargedMany_modules (store : Store NearState) (cost n : Nat) :
    (chargedMany store cost n).modules = store.modules := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => simpa [chargedMany, chargedStore] using ih (chargedStore store cost)

@[simp] theorem commitCall_funcs (cfg : WasmConfig) (store : Store NearState)
    (after : HostStore NearState) : (commitCall cfg store after).funcs = store.funcs := rfl

@[simp] theorem commitCall_modules (cfg : WasmConfig) (store : Store NearState)
    (after : HostStore NearState) : (commitCall cfg store after).modules = store.modules := rfl

/-- The four call-entry stores and final store of the composed body. -/
def bodyStages (result : HostResults) (cfg : WasmConfig) (store : Store NearState) :=
  [result.beforeInput cfg store, result.beforeStorage cfg store, result.beforeLog cfg store,
    result.beforeReturn cfg store, result.finalStore cfg store]

/-- Arbitrary host outputs cannot change function/module lookup at any stage. -/
theorem body_environments (result : HostResults) (cfg : WasmConfig) (store : Store NearState)
    (stage : Store NearState) (hstage : stage ∈ bodyStages result cfg store) :
    stage.funcs = store.funcs ∧ stage.modules = store.modules := by
  simp only [bodyStages, List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with h | h | h | h | h
  all_goals subst stage
  all_goals simp [HostResults.beforeInput, HostResults.beforeStorage, HostResults.afterInput,
    HostResults.beforeLog, HostResults.afterDrop, HostResults.afterStorage, HostResults.beforeReturn,
    HostResults.afterLog, HostResults.finalStore, chargedStore]

/-- Host lookup hypotheses are discharged by actual initialized-store facts,
including when `memory` is the configured prepared `dataMemory`. -/
theorem body_initialized_lookups (cfg : RuntimeConfig) (host : NearState) (memory : Memory)
    (result : HostResults) (stage : Store NearState)
    (hstage : stage ∈ bodyStages result cfg.wasm (initializedStore cfg host memory)) :
    stage.modules[0]? = some moduleInstance ∧
    stage.funcs[0]? = some (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn) ∧
    stage.funcs[1]? = some (.host (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).toHostFn) ∧
    stage.funcs[2]? = some (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn) ∧
    stage.funcs[3]? = some (.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn) := by
  obtain ⟨hfuncs, hmodules⟩ := body_environments result cfg.wasm _ stage hstage
  rw [hfuncs, hmodules]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The complete real body, with four single-host contracts as its only
semantic frontier. All fifteen opcodes and the administrative return are proved. -/
theorem wp_save_body (cfg : RuntimeConfig) (rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (cost : HostCosts) (result : HostResults) (written : UInt64)
    (hcredits : store.host.gas.Credits (cost.bodyBudget cfg.wasm.regularOpCost rest))
    (hinput : CallEvidence cfg.wasm (result.beforeInput cfg.wasm store) 0 [.i64 0] []
      (metered cfg.fees.numExtraBytesRecord "input" inputFn) result.input
      cost.input (cost.inputSuffix cfg.wasm.regularOpCost rest))
    (hstorage : CallEvidence cfg.wasm (result.beforeStorage cfg.wasm store) 1
      [.i64 1, .i64 0, .i64 u64Max, .i64 0, .i64 u64Max] [.i64 written]
      (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn) result.storage
      cost.storage (cost.storageSuffix cfg.wasm.regularOpCost rest))
    (hlog : CallEvidence cfg.wasm (result.beforeLog cfg.wasm store) 2 [.i64 5, .i64 1] []
      (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn) result.log
      cost.log (cost.logSuffix cfg.wasm.regularOpCost rest))
    (hreturn : CallEvidence cfg.wasm (result.beforeReturn cfg.wasm store) 3 [.i64 u64Max, .i64 0] []
      (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn) result.returned
      cost.returned rest) :
    WP cfg.wasm 16 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (cost.bodyBudget cfg.wasm.regularOpCost rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [] (result.finalStore cfg.wasm store) ∧ error = none) := by
  let post : Post := fun remaining final error => remaining = rest ∧
    final = .done [] (result.finalStore cfg.wasm store) ∧ error = none
  have hreturnCredits : (result.beforeReturn cfg.wasm store).host.gas.Credits
      (cost.returnBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    simpa [HostResults.afterLog, HostCosts.logSuffix] using hlog.credits
  have hlogCredits : (result.beforeLog cfg.wasm store).host.gas.Credits
      (cost.logBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    apply charged_credits
    simpa [HostResults.afterStorage, HostCosts.storageSuffix] using hstorage.credits
  have hstorageCredits : (result.beforeStorage cfg.wasm store).host.gas.Credits
      (cost.storageBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    simpa [HostResults.afterInput, HostCosts.inputSuffix] using hinput.credits
  have hinputCredits : (result.beforeInput cfg.wasm store).host.gas.Credits
      (cost.inputBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany_credits
    simpa [HostCosts.bodyBudget] using hcredits
  have hfinish : WP cfg.wasm 1
      (.next (atCode (result.finalStore cfg.wasm store) limits #[] saveFrame [] [])) rest post := by
    apply wp_finish_save cfg.wasm 0 rest _ limits post
    · simpa [HostResults.finalStore] using hreturn.credits
    · exact ⟨rfl, rfl, rfl⟩
  have hret := wp_evidence cfg.wasm 1 cost.returned rest _ limits _ _ [] 3 _ _ hreturn
    hreturnCredits post hfinish
  have hretConsts := wp_i64_consts cfg.wasm 2 (cost.returnBudget cfg.wasm.regularOpCost rest)
    (result.afterLog cfg.wasm store) limits [] saveFrame [] [.call 3] [u64Max, 0] post
    (by simpa [HostCosts.logSuffix, HostResults.afterLog] using hlog.credits) hret
  have hlogCall := wp_evidence cfg.wasm 4 cost.log (cost.logSuffix cfg.wasm.regularOpCost rest)
    _ limits _ _ ([.i64_const u64Max, .i64_const 0, .call 3]) 2 _ _ hlog
    hlogCredits post hretConsts
  have hlogConsts := wp_i64_consts cfg.wasm 5 (cost.logBudget cfg.wasm.regularOpCost rest)
    (result.afterDrop cfg.wasm store) limits [] saveFrame []
    [.call 2, .i64_const u64Max, .i64_const 0, .call 3] [5, 1] post
    (by
      apply charged_credits
      simpa [HostCosts.storageSuffix, HostResults.afterStorage] using hstorage.credits) hlogCall
  have hdrop := wp_drop cfg.wasm 7 (2 * cfg.wasm.regularOpCost +
      cost.logBudget cfg.wasm.regularOpCost rest) (result.afterStorage cfg.wasm store) limits
    #[] saveFrame [] [.i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    (.i64 written) post
    (by simpa [HostCosts.storageSuffix, HostResults.afterStorage] using hstorage.credits) hlogConsts
  have hstorageCall := wp_evidence cfg.wasm 8 cost.storage
    (cost.storageSuffix cfg.wasm.regularOpCost rest) _ limits _ _
    [.drop, .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    1 _ _ hstorage hstorageCredits post hdrop
  have hstorageConsts := wp_i64_consts cfg.wasm 9
    (cost.storageBudget cfg.wasm.regularOpCost rest) (result.afterInput cfg.wasm store)
    limits [] saveFrame []
    [.call 1, .drop, .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    [1, 0, u64Max, 0, u64Max] post
    (by simpa [HostCosts.inputSuffix, HostResults.afterInput] using hinput.credits) hstorageCall
  have hinputCall := wp_evidence cfg.wasm 14 cost.input
    (cost.inputSuffix cfg.wasm.regularOpCost rest) _ limits _ _
    [.i64_const 1, .i64_const 0, .i64_const u64Max, .i64_const 0, .i64_const u64Max, .call 1, .drop,
      .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    0 _ _ hinput hinputCredits post hstorageConsts
  have hbody := wp_i64_consts cfg.wasm 15 (cost.inputBudget cfg.wasm.regularOpCost rest)
    store limits [] saveFrame []
    [.call 0, .i64_const 1, .i64_const 0, .i64_const u64Max, .i64_const 0, .i64_const u64Max,
      .call 1, .drop, .i64_const 5, .i64_const 1, .call 2, .i64_const u64Max, .i64_const 0, .call 3]
    [0] post (by simpa [HostCosts.bodyBudget] using hcredits) hinputCall
  simpa [HostCosts.bodyBudget, post, module, u64Max] using hbody

end WNear.Skeleton
