import NearVM.Run
import NearVM.GasBudget

/-!
# From local budget simulations to complete metered runs

The interpreter can observe `NearContext`, including `prepaid_gas`, so changing
that context is not a budget comparison. `Related` fixes the whole guest-visible
context while allowing the internal gas counter's limits to differ. Its extra
relation parameter records the caller's memory, storage and control invariant.

No arbitrary host is assumed budget-insensitive or log-monotone. The lifting
lemmas take these as explicit *one-step* premises; proving them for the hosts a
module uses is the remaining obligation at each application.
-/
namespace Wasm.Near.MeteredPrefix

/-- One actual metered transition, including instruction and frame charges. -/
def advance (cfg : WasmConfig) : Machine → Machine × Option FunctionCallError
  | .next c =>
    let charged := chargeConfig c (nextInstructionGas cfg c)
    match charged.2 with
    | some error => (.next charged.1, some (.hostError error))
    | none =>
      let next := Exec.step charged.1
      let charged' := chargeWasm next (frameTransitionGas cfg charged.1 next)
      (charged'.1, charged'.2.map FunctionCallError.hostError)
  | m => (m, none)

/-- Factorization of the existing runner, not a replacement interpreter. -/
theorem run_succ (cfg : WasmConfig) (fuel : Nat) (m : Machine) :
    runMetered cfg (fuel + 1) m =
      match (advance cfg m).2 with
      | some error => ((advance cfg m).1, some error)
      | none => runMetered cfg fuel (advance cfg m).1 := by
  cases m with
  | done values store => simp only [advance, runMetered_done]
  | trap reason store => simp only [advance, runMetered_trapped]
  | next c =>
    simp only [advance, runMetered]
    cases hop : (chargeConfig c (nextInstructionGas cfg c)).2 with
    | some error => rfl
    | none =>
      simp only
      cases hframe : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
        (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
          (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 <;> rfl

/-- A transition result which the runner cannot continue executing. -/
def Stopped (result : Machine × Option FunctionCallError) : Prop :=
  result.2 ≠ none ∨ ∀ c, result.1 ≠ .next c

theorem run_succ_stopped (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : Stopped (advance cfg m)) :
    runMetered cfg (fuel + 1) m = advance cfg m := by
  rw [run_succ]
  cases he : (advance cfg m).2 with
  | some error => exact Prod.ext rfl he.symm
  | none =>
    obtain herror | hterminal := h
    · exact False.elim (herror he)
    · cases hm : (advance cfg m).1 with
      | next c => exact False.elim (hterminal c hm)
      | done values store =>
        rw [runMetered_done]
        exact Prod.ext hm.symm he.symm
      | trap reason store =>
        rw [runMetered_trapped]
        exact Prod.ext hm.symm he.symm

/-- Both protocol gas errors, with their distinct exhaustion precedence. -/
def GasError (error : HostError) : Prop :=
  error = .gasExceeded ∨ error = .gasLimitExceeded

/-- Gas can fail in the runner's own charge, or inside a metered host. The
latter is a Wasm host trap, whose structured error `trapError` exposes. -/
def GasFailure (result : Machine × Option FunctionCallError) : Prop :=
  ∃ error, GasError error ∧
    (result.2 = some (.hostError error) ∨
      (result.2 = none ∧ ∃ reason store, result.1 = .trap reason store ∧
        trapError reason store.host = .hostError error))

theorem GasFailure.stopped {result : Machine × Option FunctionCallError}
    (h : GasFailure result) : Stopped result := by
  obtain ⟨error, _, houter | ⟨_, reason, store, htrap, _⟩⟩ := h
  · exact Or.inl (by rw [houter]; intro h; cases h)
  · right
    intro c hnext
    rw [htrap] at hnext
    cases hnext

theorem GasFailure.not_fuel {result : Machine × Option FunctionCallError}
    (h : GasFailure result) : result.2 ≠ some (.executionIssue .fuelExhausted) := by
  obtain ⟨error, _, houter | ⟨hnone, _⟩⟩ := h
  · rw [houter]; intro h; cases h
  · rw [hnone]; intro h; cases h

/-- Both internal charge failures and host gas traps are reported as protocol
gas failures by the real execution boundary. -/
theorem GasFailure.aborted {result : Machine × Option FunctionCallError}
    (h : GasFailure result) (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) :
    ∃ error, GasError error ∧
      (outcomeOfExecution ctx storage result.1 result.2).aborted = some (.hostError error) := by
  obtain ⟨error, hgas, houter | ⟨hnone, reason, store, htrap, herr⟩⟩ := h
  · exact ⟨error, hgas, by simp only [outcomeOfExecution, houter]⟩
  · exact ⟨error, hgas, by simp only [outcomeOfExecution, hnone, htrap, herr, StepResult.host]⟩

/-- The observable terminal shape, without internal metering state. -/
inductive Control where
  | running
  | done (values : List Value)
  | trap (reason : Trap)

def control : Machine → Control
  | .next _ => .running
  | .done values _ => .done values
  | .trap reason _ => .trap reason

/-- Common-prefix configurations keep all guest-visible context and accounting
fixed. Only the counter's internal prepaid/burn limits may be larger. -/
structure Related (R : Machine → Machine → Prop) (small large : Machine) : Prop where
  state : R small large
  control : control small = control large
  context : small.host.context = large.host.context
  logs : small.host.logs = large.host.logs
  gas : GasCounter.Below small.host.gas large.host.gas

abbrev LogPrefix (small large : Machine) : Prop :=
  List.IsPrefix small.host.logs large.host.logs

/-- The sole program-simulation premise compares one metered transition. A
small-budget gas failure may stop within a host, after appending some logs. -/
def StepSimulation (cfg : WasmConfig) (R : Machine → Machine → Prop) : Prop :=
  ∀ small large, Related R small large →
    (Related R (advance cfg small).1 (advance cfg large).1 ∧
      (advance cfg small).2 = (advance cfg large).2) ∨
    (GasFailure (advance cfg small) ∧ LogPrefix (advance cfg small).1 (advance cfg large).1)

/-- A local host/log obligation, independently of budget comparison. -/
def LogsMonotone (cfg : WasmConfig) (I : Machine → Prop) : Prop :=
  ∀ m, I m → LogPrefix m (advance cfg m).1

/-- A reachable-state invariant lets applications constrain the installed host
functions rather than requiring log monotonicity for arbitrary stores. -/
def AdvanceInvariant (cfg : WasmConfig) (I : Machine → Prop) : Prop :=
  ∀ m, I m → I (advance cfg m).1

/-- The low run either ends alongside the high run, or stops at a protocol gas
failure with logs that are a prefix of the high run's final logs. -/
def MatchesOrGas (R : Machine → Machine → Prop)
    (small large : Machine × Option FunctionCallError) : Prop :=
  (Related R small.1 large.1 ∧ small.2 = large.2) ∨
    (GasFailure small ∧ LogPrefix small.1 large.1)

/-- Local log monotonicity lifts to every actual runner prefix, including
charge failures, host traps, normal returns and fuel exhaustion. -/
theorem run_logs_monotone (cfg : WasmConfig) (I : Machine → Prop)
    (hclosed : AdvanceInvariant cfg I) (hlogs : LogsMonotone cfg I)
    (fuel : Nat) (m : Machine) (hinv : I m) : LogPrefix m (runMetered cfg fuel m).1 := by
  induction fuel generalizing m with
  | zero => cases m <;> exact ⟨[], List.append_nil _⟩
  | succ fuel ih =>
    rw [run_succ]
    cases he : (advance cfg m).2 with
    | some error => exact hlogs m hinv
    | none => exact (hlogs m hinv).trans (ih (advance cfg m).1 (hclosed m hinv))

/-- After its first transition the high run only extends its log prefix. -/
theorem advance_logs_prefix_run (cfg : WasmConfig) (I : Machine → Prop)
    (hclosed : AdvanceInvariant cfg I) (hlogs : LogsMonotone cfg I)
    (fuel : Nat) (m : Machine) (hinv : I m) :
    LogPrefix (advance cfg m).1 (runMetered cfg (fuel + 1) m).1 := by
  rw [run_succ]
  cases he : (advance cfg m).2 with
  | some error => exact ⟨[], List.append_nil _⟩
  | none => exact run_logs_monotone cfg I hclosed hlogs fuel _ (hclosed m hinv)

/-- Complete simulation is derived from local transition compatibility by fuel
induction. No whole-run correctness or below-budget conclusion is a premise. -/
theorem run_simulation (cfg : WasmConfig) (R : Machine → Machine → Prop)
    (hsim : StepSimulation cfg R) (I : Machine → Prop)
    (hclosed : AdvanceInvariant cfg I) (hlogs : LogsMonotone cfg I)
    (fuel : Nat) (small large : Machine) (hrel : Related R small large) (hinv : I large) :
    MatchesOrGas R (runMetered cfg fuel small) (runMetered cfg fuel large) := by
  induction fuel generalizing small large with
  | zero =>
    left
    have hsmall : (runMetered cfg 0 small).1 = small := by cases small <;> rfl
    have hlarge : (runMetered cfg 0 large).1 = large := by cases large <;> rfl
    refine ⟨by simpa only [hsmall, hlarge] using hrel, ?_⟩
    have hcontrol := hrel.control
    cases small <;> cases large <;> cases hcontrol <;> rfl
  | succ fuel ih =>
    rcases hsim small large hrel with ⟨hnext, herr⟩ | ⟨hgas, hprefix⟩
    · rw [run_succ cfg fuel small, run_succ cfg fuel large, herr]
      cases he : (advance cfg large).2 with
      | none => exact ih _ _ hnext (hclosed large hinv)
      | some error =>
        left
        exact ⟨hnext, rfl⟩
    · right
      have hstop := run_succ_stopped cfg fuel small hgas.stopped
      refine ⟨by simpa only [hstop] using hgas, ?_⟩
      rw [hstop]
      exact hprefix.trans (advance_logs_prefix_run cfg I hclosed hlogs fuel large hinv)

/-- Fuel sufficiency on the high run excludes a low-run fuel error as well:
the low run either matches it or has a protocol gas failure with prefix logs. -/
theorem run_simulation_no_fuel (cfg : WasmConfig) (R : Machine → Machine → Prop)
    (hsim : StepSimulation cfg R) (I : Machine → Prop)
    (hclosed : AdvanceInvariant cfg I) (hlogs : LogsMonotone cfg I)
    (fuel : Nat) (small large : Machine) (hrel : Related R small large) (hinv : I large)
    (hhigh : (runMetered cfg fuel large).2 ≠ some (.executionIssue .fuelExhausted)) :
    MatchesOrGas R (runMetered cfg fuel small) (runMetered cfg fuel large) ∧
      (runMetered cfg fuel small).2 ≠ some (.executionIssue .fuelExhausted) := by
  have h := run_simulation cfg R hsim I hclosed hlogs fuel small large hrel hinv
  refine ⟨h, ?_⟩
  rcases h with ⟨_, herr⟩ | ⟨hgas, _⟩
  · rw [herr]
    exact hhigh
  · exact hgas.not_fuel

end Wasm.Near.MeteredPrefix
