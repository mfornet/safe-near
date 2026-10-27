import Skeleton.FunctionalInvariant

/-!
# Actual startup and body budget simulation

Loading and entry activation use the original guest-visible context. Only the
reference counter's internal limits are enlarged. Startup gas failures are
classified directly; successful startup establishes the closed body invariant.
-/
namespace WNear.Skeleton.StartupSimulation
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget MeteredHostBudget
open MeteredHosts BudgetSimulation FunctionalInvariant NearInterface

/-- The actual loading prefix, including its short-circuiting failure state. -/
def loaded (host : NearState) : NearState := (applyCharges host (loadingCharges 0)).1

def active (cfg : RuntimeConfig) (host : NearState) : NearState :=
  (chargeHost (loaded host) (8 * cfg.wasm.regularOpCost)).1

def body (cfg : RuntimeConfig) (host : NearState) : Machine :=
  .next (entryConfig cfg (active cfg host))

/-- The reference pays the same real loading and activation plans. -/
def reference (ctx : Context) (raw : Storage) (budget fuel : Nat) : Machine × Option FunctionCallError :=
  runMetered ctx.protocol.wasm fuel (body ctx.protocol (enlargeHost (origin ctx raw) budget))

private theorem loading_burns : ∀ c ∈ loadingCharges 0, BurnsOnly c := by
  simp [loadingCharges, BurnsOnly]

/-- Startup preserves every field required by the original empty-base argument. -/
theorem active_preEq (cfg : RuntimeConfig) (host : NearState) : PreEq host (active cfg host) :=
  (PreEq.charges host _ loading_burns).trans (PreEq.charged _ _)

/-- Successful low startup replays both real charge phases in the reference. -/
theorem active_below (cfg : RuntimeConfig) (host : NearState) (budget : Nat)
    (hl : (applyCharges host (loadingCharges 0)).2 = none)
    (ha : (chargeHost (loaded host) (8 * cfg.wasm.regularOpCost)).2 = none) :
    Budget.HostBelow (active cfg host) (active cfg (enlargeHost host budget)) := by
  have hp := Budget.applyCharges_below (enlargeHost_below host budget) _ loading_burns hl
  exact (chargeHost_below hp.2 _ ha).2

/-- Successful startup establishes actual active-body relatedness. -/
theorem active_related (ctx : Context) (raw : Storage) (budget : Nat)
    (hl : (applyCharges (origin ctx raw) (loadingCharges 0)).2 = none)
    (ha : (chargeHost (loaded (origin ctx raw)) (8 * ctx.protocol.wasm.regularOpCost)).2 = none) :
    Related (SimulationRelation ctx raw execLimits)
      (body ctx.protocol (origin ctx raw)) (body ctx.protocol (enlargeHost (origin ctx raw) budget)) := by
  have hb : MachineBelow (body ctx.protocol (origin ctx raw))
      (body ctx.protocol (enlargeHost (origin ctx raw) budget)) :=
    .next ⟨⟨rfl, active_below ctx.protocol (origin ctx raw) budget hl ha⟩, rfl, rfl⟩
  have hf := active_preEq ctx.protocol (origin ctx raw)
  have hr := hb.related
  refine ⟨⟨hb, ?_⟩, hr.control, hr.context, hr.logs, hr.gas⟩
  refine ⟨⟨0, by decide⟩, 0, _, rfl, initialized_installed _ _ _, ?_⟩
  exact ⟨hf.isView, hf.issue, fun _ => ⟨hf, rfl⟩, by intro h; change 2 ≤ 0 at h; omega⟩

/-- No funded-host or run-result premise is used to simulate the active body. -/
theorem active_runSimulation (ctx : Context) (raw : Storage) (budget fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none)
    (hfuel : 16 ≤ fuel)
    (hl : (applyCharges (origin ctx raw) (loadingCharges 0)).2 = none)
    (ha : (chargeHost (loaded (origin ctx raw)) (8 * ctx.protocol.wasm.regularOpCost)).2 = none) :
    MatchesOrGas (SimulationRelation ctx raw execLimits)
      (runMetered ctx.protocol.wasm fuel (body ctx.protocol (origin ctx raw)))
      (reference ctx raw budget fuel) ∧
    (runMetered ctx.protocol.wasm fuel (body ctx.protocol (origin ctx raw))).2 ≠
      some (.executionIssue .fuelExhausted) := by
  exact runSimulation ctx raw execLimits hwf hpages hentries hselected hproof fuel _ _
    (active_related ctx raw budget hl ha) (by change 16 ≤ fuel; exact hfuel)

/-- Expose actual activation without assuming a credit budget for the low run. -/
theorem runInitialized_active (cfg : RuntimeConfig) (host : NearState) (fuel : Nat)
    (ha : (chargeHost host (8 * cfg.wasm.regularOpCost)).2 = none) :
    runInitialized cfg.wasm fuel (.next (entryConfig cfg host)) =
      runMetered cfg.wasm fuel (.next (entryConfig cfg (chargeHost host (8 * cfg.wasm.regularOpCost)).1)) := by
  simp only [runInitialized, entryCost_save]
  change (match (chargeHost host (8 * cfg.wasm.regularOpCost)).2 with
    | some error => _ | none => _) = _
  rw [ha]
  rfl

/-- Gas reserved in an enlarged initial counter survives real startup. -/
theorem reference_credits (ctx : Context) (raw : Storage) (rest : Nat) :
    let cost := burnSum (origin ctx raw).extCosts (loadingCharges 0) +
      (8 * ctx.protocol.wasm.regularOpCost + rest)
    (active ctx.protocol (enlargeHost (origin ctx raw) cost)).gas.Credits rest := by
  let cost := burnSum (origin ctx raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + rest)
  have hc := enlarged_initial_credits ctx.protocol (Near.Boundary.toVMContext ctx) raw cost
  have hl := applyCharges_credits (enlargeHost (origin ctx raw) cost) (loadingCharges 0)
    (8 * ctx.protocol.wasm.regularOpCost + rest) loading_burns hc
  exact (GasCounter.burn_credits _ _ rest hl.2.2.2.2).2.2.2

/-- Loading failure is the precise actual VM early exit. -/
theorem runAttempt_loading_error (cfg : RuntimeConfig) (vm : VMContext) (raw : Storage)
    (fuel : Nat) (error : HostError)
    (htypes : ∀ n, cfg.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, cfg.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hl : (applyCharges (vm.toNearState cfg raw) (loadingCharges 0)).2 = some error) :
    runAttempt cfg module 0 "save" vm raw fuel =
      VMOutcome.failedBefore vm raw (loaded (vm.toNearState cfg raw)).gas.burnt (.hostError error)
        (loaded (vm.toNearState cfg raw)).gasProfile := by
  have hp : applyCharges (vm.toNearState cfg raw) (loadingCharges 0) =
      (loaded (vm.toNearState cfg raw), some error) := Prod.ext rfl hl
  simp only [runAttempt, show "save".isEmpty = false by decide, Bool.false_eq_true, ↓reduceIte,
    prepared_limits cfg.wasm.limits htypes hfunctions, hp]

/-- Early startup failures retain no logs, expose a protocol gas error, and
have the empty receipt graph accepted by the public runner. -/
def StartupGas (outcome : VMOutcome) : Prop :=
  ∃ error, GasError error ∧ outcome.aborted = some (.hostError error) ∧ outcome.logs = [] ∧ outcome.receiptsValid = true

/-- Actual startup either stops for protocol gas, or exposes the real active
body result together with whole-body replay and the absence of a fuel error. -/
def AttemptReplay (ctx : Context) (raw : Storage) (budget fuel : Nat) : Prop :=
  StartupGas (runAttempt ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw fuel) ∨
    ∃ result : Machine × Option FunctionCallError,
      runAttempt ctx.protocol module 0 "save" (Near.Boundary.toVMContext ctx) raw fuel =
        outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2 ∧
      MatchesOrGas (SimulationRelation ctx raw execLimits) result (reference ctx raw budget fuel) ∧
      result.2 ≠ some (.executionIssue .fuelExhausted)

/-- Full actual attempt simulation through loading, preparation, linking,
entry activation and the body. No sufficient-gas assumption is made on the
original attempt, and all host/resource rejection branches remain included. -/
theorem runAttempt_replay (ctx : Context) (raw : Storage) (budget fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpositive : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hminmax : ctx.protocol.wasm.limits.initialMemoryPages ≤ ctx.protocol.wasm.limits.maxMemoryPages)
    (hmax : ctx.protocol.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, ctx.protocol.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, ctx.protocol.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none)
    (hfuel : 16 ≤ fuel) : AttemptReplay ctx raw budget fuel := by
  cases hl : (applyCharges (origin ctx raw) (loadingCharges 0)).2 with
  | some error =>
    left
    have hg := Budget.applyCharges_error_is_gas (origin ctx raw) _ loading_burns hl
    refine ⟨error, hg.elim Or.inr Or.inl, ?_⟩
    rw [runAttempt_loading_error ctx.protocol (Near.Boundary.toVMContext ctx) raw fuel error htypes hfunctions hl]
    exact ⟨rfl, rfl, rfl⟩
  | none =>
    have hload : applyCharges (origin ctx raw) (loadingCharges 0) = (loaded (origin ctx raw), none) :=
      Prod.ext rfl hl
    have hattempt := runAttempt_save ctx.protocol (Near.Boundary.toVMContext ctx) raw fuel
      (loaded (origin ctx raw)) hpositive hminmax hmax htypes hfunctions hload
    cases ha : (chargeHost (loaded (origin ctx raw)) (8 * ctx.protocol.wasm.regularOpCost)).2 with
    | some error =>
      left
      have hg := GasCounter.deduct_error_is_gas (loaded (origin ctx raw)).gas _ _ ha
      refine ⟨error, hg.elim Or.inr Or.inl, ?_⟩
      rw [hattempt]
      have hinit : runInitialized ctx.protocol.wasm fuel (.next (entryConfig ctx.protocol (loaded (origin ctx raw)))) =
          (.next (entryConfig ctx.protocol (active ctx.protocol (origin ctx raw))), some (.hostError error)) := by
        simp only [runInitialized, entryCost_save]
        change (match (chargeHost (loaded (origin ctx raw)) (8 * ctx.protocol.wasm.regularOpCost)).2 with
          | some error => _ | none => _) = _
        rw [ha]
        rfl
      rw [hinit]
      have hlogs : (active ctx.protocol (origin ctx raw)).logs = [] := by
        have hf := congrArg NearState.logs (applyCharges_frame (origin ctx raw) _ loading_burns)
        exact hf
      refine ⟨rfl, ?_, rfl⟩
      change logsOf (active ctx.protocol (origin ctx raw)) = []
      rw [show logsOf (active ctx.protocol (origin ctx raw)) =
        (active ctx.protocol (origin ctx raw)).logs.map (fun bytes => (String.fromUTF8? ⟨bytes.toArray⟩).getD "") from rfl, hlogs]
      rfl
    | none =>
      right
      have hr := active_runSimulation ctx raw budget fuel hwf hpositive hentries hselected hproof hfuel hl ha
      refine ⟨runMetered ctx.protocol.wasm fuel (body ctx.protocol (origin ctx raw)), ?_, hr.1, hr.2⟩
      rw [hattempt, runInitialized_active ctx.protocol (loaded (origin ctx raw)) fuel ha]
      rfl

/-- Startup does not synchronize or otherwise alter guest-visible context;
its counter changes are entirely internal. -/
theorem active_context (cfg : RuntimeConfig) (host : NearState) :
    (active cfg host).context = host.context := by
  have hf := congrArg NearState.context (applyCharges_frame host _ loading_burns)
  exact hf

/-- The enlarged reference really passes loading and activation, retaining
any chosen finite body reservation. This asserts no funded body outcome. -/
theorem reference_startup_credits (ctx : Context) (raw : Storage) (rest : Nat) :
    let cost := burnSum (origin ctx raw).extCosts (loadingCharges 0) +
      (8 * ctx.protocol.wasm.regularOpCost + rest)
    let high := enlargeHost (origin ctx raw) cost
    (applyCharges high (loadingCharges 0)).2 = none ∧
      (chargeHost (loaded high) (8 * ctx.protocol.wasm.regularOpCost)).2 = none ∧
      (active ctx.protocol high).gas.Credits rest := by
  let cost := burnSum (origin ctx raw).extCosts (loadingCharges 0) +
    (8 * ctx.protocol.wasm.regularOpCost + rest)
  have hc := enlarged_initial_credits ctx.protocol (Near.Boundary.toVMContext ctx) raw cost
  have hl := applyCharges_credits (enlargeHost (origin ctx raw) cost) (loadingCharges 0)
    (8 * ctx.protocol.wasm.regularOpCost + rest) loading_burns hc
  have ha := GasCounter.burn_credits _ _ rest hl.2.2.2.2
  exact ⟨hl.1, ha.1, ha.2.2.2⟩

theorem StartupGas.receipts_valid {outcome : VMOutcome} (h : StartupGas outcome) :
    outcome.receiptsValid = true := by
  obtain ⟨_, _, _, _, hv⟩ := h
  exact hv

theorem StartupGas.not_fuel {outcome : VMOutcome} (h : StartupGas outcome) :
    outcome.aborted ≠ some (.executionIssue .fuelExhausted) := by
  obtain ⟨error, _, he, _, _⟩ := h
  rw [he]
  intro h
  cases h

/-- Empty startup logs are a prefix of every reference outcome's logs. -/
theorem StartupGas.logs_prefix {outcome : VMOutcome} (h : StartupGas outcome) (logs : List String) :
    List.IsPrefix outcome.logs logs := by
  obtain ⟨_, _, _, hl, _⟩ := h
  rw [hl]
  exact ⟨logs, rfl⟩

end WNear.Skeleton.StartupSimulation
