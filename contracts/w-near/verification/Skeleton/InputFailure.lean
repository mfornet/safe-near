import Skeleton.Body
import NearVM.MeteredTrap

/-!
# The early input-size failure

The first constant and actual metered `input` call are proved to trap on an
oversized input register. No storage, log, return, or suffix-execution premise
is used. Protocol trap classification is kept separate from machine execution.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- Input rejects after paying its actual two fixed external charges. -/
def inputFailurePaid (cfg : WasmConfig) (store : Store NearState) : HostStore NearState :=
  MeteredHosts.Input.paid (inputBefore cfg store moduleInstance)

/-- Compose the existing input rejection contract with the real call/trap rule. -/
theorem wp_call_input_too_long (cfg : WasmConfig) (extra fuel rest : Nat)
    (store : Store NearState) (limits : ExecLimits) (code : List Instr)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[0]? = some (.host (metered extra "input" inputFn).toHostFn))
    (hlimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = false)
    (hcredits : store.host.gas.Credits
      (cfg.regularOpCost + (MeteredHosts.Input.cost store.host + rest))) :
    WP cfg (fuel + 1)
      (.next (atCode store limits #[.i64 0] saveFrame [] (.call 0 :: code)))
      (cfg.regularOpCost + (MeteredHosts.Input.cost store.host + rest))
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host "input: register size exceeded")
          (commitCall cfg store (inputFailurePaid cfg store)) ∧ error = none) := by
  let before := inputBefore cfg store moduleInstance
  have hc := Pays.chargeConfig (atCode store {} #[] saveFrame [] []) cfg.regularOpCost
    (MeteredHosts.Input.cost store.host + rest) hcredits
  have hi : before.host.gas.Credits (MeteredHosts.Input.cost before.host + rest) := hc.2.2.2.2
  have hp := MeteredHosts.Input.paid_credits before rest hi
  have hinvoke := MeteredHosts.Input.metered_too_long extra before 0 hp.1 (by decide) hlimit
  apply wp_call_host_trap cfg fuel (MeteredHosts.Input.cost store.host) rest store limits []
    [.i64 0] saveFrame [] code 0 0 moduleInstance (metered extra "input" inputFn)
    (inputFailurePaid cfg store) "input: register size exceeded" hmodule rfl hfn rfl
    hcredits hinvoke (Nat.le_of_eq hp.2.1) ?_ hp.2.2.2
  change (inputFailurePaid cfg store).host.gas.burnt + (inputFailurePaid cfg store).host.gas.promises ≤
    before.host.gas.burnt + before.host.gas.promises + MeteredHosts.Input.cost before.host
  have hb := hp.2.1
  have hr := hp.2.2.1
  change (inputFailurePaid cfg store).host.gas.burnt =
    before.host.gas.burnt + MeteredHosts.Input.cost before.host at hb
  change (inputFailurePaid cfg store).host.gas.promises = before.host.gas.promises at hr
  omega

/-- The constant's charge precedes the failing input call and its two charges. -/
def inputFailureBudget (cfg : WasmConfig) (store : Store NearState) (rest : Nat) :=
  2 * cfg.regularOpCost + MeteredHosts.Input.cost store.host + rest

/-- No host except input has executed in this exact final store. -/
def inputFailureStore (cfg : WasmConfig) (store : Store NearState) : Store NearState :=
  let pushed := chargedStore store cfg.regularOpCost
  commitCall cfg pushed (inputFailurePaid cfg pushed)

/-- The body reaches the early trap in exactly two steps, retaining all
unused credits. The thirteen later instructions are never assumed or executed. -/
theorem wp_save_input_too_long (cfg : RuntimeConfig) (store : Store NearState)
    (limits : ExecLimits) (rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[0]? = some
      (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hlimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = false)
    (hcredits : store.host.gas.Credits (inputFailureBudget cfg.wasm store rest)) :
    WP cfg.wasm 2 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body))
      (inputFailureBudget cfg.wasm store rest)
      (fun remaining final error => remaining = rest ∧ final =
        .trap (.host "input: register size exceeded") (inputFailureStore cfg.wasm store) ∧ error = none) := by
  let tail := module.funcs[0]!.body.drop 2
  have hc : store.host.gas.Credits
      (cfg.wasm.regularOpCost +
        (cfg.wasm.regularOpCost + (MeteredHosts.Input.cost store.host + rest))) := by
    simpa [inputFailureBudget, Nat.add_assoc, Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm, two_mul] using hcredits
  have hp := Pays.chargeWasm (.done [] store) cfg.wasm.regularOpCost
    (cfg.wasm.regularOpCost + (MeteredHosts.Input.cost store.host + rest)) hc
  have hcall := wp_call_input_too_long cfg.wasm cfg.fees.numExtraBytesRecord 0 rest
    (chargedStore store cfg.wasm.regularOpCost) limits tail hmodule hfn hlimit hp.2.2.2.2
  have hstep := wp_i64_const cfg.wasm 1
    (cfg.wasm.regularOpCost + (MeteredHosts.Input.cost store.host + rest)) store limits #[] saveFrame []
    (.call 0 :: tail) 0 _ hc hcall
  simpa [inputFailureBudget, inputFailureStore, tail, module, Nat.add_assoc,
    Nat.add_mul, Nat.add_comm, Nat.add_left_comm, two_mul] using hstep

/-- Rejection retains functional state and the pre-existing error markers;
only charges, diagnostic gas and the observable used-gas field may differ. -/
theorem inputFailureStore_frame (cfg : WasmConfig) (store : Store NearState) :
    let after := (inputFailureStore cfg store).host
    after.lastError = store.host.lastError ∧
    after.lastExecutionIssue = store.host.lastExecutionIssue ∧
    after.logs = store.host.logs ∧ after.storage = store.host.storage ∧
    after.registers = store.host.registers := by
  let before := inputBefore cfg (chargedStore store cfg.regularOpCost) moduleInstance
  have hf := congrArg (fun host : NearState =>
      (host.lastError, host.lastExecutionIssue, host.logs, host.storage, host.registers))
    (MeteredHosts.applyCharges_frame before.host [.ext "base", .ext "write_register_base"]
      (by simp [MeteredHosts.BurnsOnly]))
  simpa only [Prod.mk.injEq, before, inputFailureStore, commitCall_host, inputFailurePaid,
    MeteredHosts.Input.paid, inputBefore, chargedStore, chargeHost] using hf

/-- With fresh error markers the raw host trap is precisely the guest panic
reported at this boundary. Stale markers are not silently excluded. -/
theorem inputFailure_error (cfg : WasmConfig) (store : Store NearState)
    (herror : store.host.lastError = none) (hissue : store.host.lastExecutionIssue = none) :
    trapError (.host "input: register size exceeded") (inputFailureStore cfg store).host =
      .hostError (.guestPanic "input: register size exceeded") := by
  have hf := inputFailureStore_frame cfg store
  simp only [trapError, hf.1, hf.2.1, herror, hissue]

/-- The exact interpreter run follows from the two-instruction contract. -/
theorem run_save_input_too_long (cfg : RuntimeConfig) (store : Store NearState)
    (limits : ExecLimits) (rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[0]? = some
      (.host (metered cfg.fees.numExtraBytesRecord "input" inputFn).toHostFn))
    (hlimit : withinLimit store.host.config.maxRegisterLen store.host.context.input.length = false)
    (hcredits : store.host.gas.Credits (inputFailureBudget cfg.wasm store rest)) :
    runMetered cfg.wasm 2 (.next (atCode store limits #[] saveFrame [] module.funcs[0]!.body)) =
      (.trap (.host "input: register size exceeded") (inputFailureStore cfg.wasm store), none) := by
  obtain ⟨_, hpost, _⟩ := (wp_save_input_too_long cfg store limits rest hmodule hfn hlimit hcredits).result
  exact Prod.ext hpost.2.1 hpost.2.2

/-- The classified failed outcome is deterministic under the explicitly fresh
host error markers. Account rollback is the existing runtime boundary's rule. -/
theorem inputFailure_outcome (cfg : WasmConfig) (ctx : VMContext)
    (raw : List (List UInt8 × List UInt8)) (store : Store NearState)
    (herror : store.host.lastError = none) (hissue : store.host.lastExecutionIssue = none) :
    (outcomeOfExecution ctx raw
      (.trap (.host "input: register size exceeded") (inputFailureStore cfg store)) none).aborted =
      some (.hostError (.guestPanic "input: register size exceeded")) := by
  simp only [outcomeOfExecution, StepResult.host, inputFailure_error cfg store herror hissue]

end WNear.Skeleton
