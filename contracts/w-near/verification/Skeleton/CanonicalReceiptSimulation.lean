import Skeleton.CanonicalSimulation
import Skeleton.ReceiptSimulation

/-!
# Actual canonical startup and public receipt budget replay

The guest context and original raw storage remain fixed. Canonical primitive
readiness replaces the empty-base restriction in the actual body simulation;
loading, activation and all public receipt checks are still the real runtime.
-/
namespace WNear.Skeleton.CanonicalReceiptSimulation
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget NearInterface
open MeteredHosts BudgetSimulation FunctionalInvariant StartupSimulation

private theorem loading_burns : ∀ c ∈ loadingCharges 0, BurnsOnly c := by
  simp [loadingCharges, BurnsOnly]

/-- Arbitrary canonical body replay starts after both actual startup charges. -/
theorem active_runSimulation (ctx : Context) (raw : Storage) (budget fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw)
    (hfuel : 16 ≤ fuel)
    (hl : (applyCharges (origin ctx raw) (loadingCharges 0)).2 = none)
    (ha : (chargeHost (loaded (origin ctx raw)) (8 * ctx.protocol.wasm.regularOpCost)).2 = none) :
    MatchesOrGas (SimulationRelation ctx raw execLimits)
      (runMetered ctx.protocol.wasm fuel (body ctx.protocol (origin ctx raw)))
      (reference ctx raw budget fuel) ∧
    (runMetered ctx.protocol.wasm fuel (body ctx.protocol (origin ctx raw))).2 ≠
      some (.executionIssue .fuelExhausted) := by
  exact CanonicalSimulation.runSimulation ctx raw execLimits hwf hpages hnodes hproof fuel _ _
    (active_related ctx raw budget hl ha) (by change 16 ≤ fuel; exact hfuel)

/-- The actual attempt either stops during startup for protocol gas, or yields
its real body result with canonical whole-body replay and no runner fuel error. -/
theorem runAttempt_replay (ctx : Context) (raw : Storage) (budget fuel : Nat)
    (hwf : ctx.WF raw.toFinset) (hpositive : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hminmax : ctx.protocol.wasm.limits.initialMemoryPages ≤ ctx.protocol.wasm.limits.maxMemoryPages)
    (hmax : ctx.protocol.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, ctx.protocol.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, ctx.protocol.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw)
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
      have hr := active_runSimulation ctx raw budget fuel hwf hpositive hnodes hproof hfuel hl ha
      refine ⟨runMetered ctx.protocol.wasm fuel (body ctx.protocol (origin ctx raw)), ?_, hr.1, hr.2⟩
      rw [hattempt, runInitialized_active ctx.protocol (loaded (origin ctx raw)) fuel ha]
      rfl

/-- Actual default-fuel receipt execution agrees with the unchanged auxiliary
reference observation or aborts for gas with rollback and reference-prefix logs.
No empty-base/selected-key condition or high-model callback is assumed. -/
theorem execOn_replay (ctx : Context) (raw : Storage) (budget : Nat)
    (hmethod : ctx.method = "save")
    (hwf : ctx.WF raw.toFinset) (hpositive : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hminmax : ctx.protocol.wasm.limits.initialMemoryPages ≤ ctx.protocol.wasm.limits.maxMemoryPages)
    (hmax : ctx.protocol.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, ctx.protocol.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, ctx.protocol.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw) :
    let observed := Near.Boundary.execOn code raw ctx
    observed = ReceiptSimulation.referenceObservation ctx raw budget ∨
      (observed.outcome = .error .outOfGas ∧ RolledBack ctx raw.toFinset observed ∧
        observed.logs <+: (ReceiptSimulation.referenceObservation ctx raw budget).logs) := by
  have hexec := Near.Boundary.execOn_observeChecked code ctx raw rfl
  change Near.Boundary.execOn code raw ctx = Near.Boundary.observeChecked code.codeOf ctx raw
    (runAttempt ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw
      (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx))) at hexec
  rw [hmethod] at hexec
  change Near.Boundary.execOn code raw ctx = ReceiptSimulation.referenceObservation ctx raw budget ∨ _
  rw [hexec]
  have hr := runAttempt_replay ctx raw budget
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hwf hpositive hminmax hmax htypes hfunctions
    hnodes hproof (fuelFor_save _ _)
  rcases hr with hstartup | ⟨result, heq, hsim, _⟩
  · right
    obtain ⟨error, hg, ha, hl, hv⟩ := hstartup
    apply Near.Boundary.observeChecked_protocolGas code.codeOf ctx raw _ error _ hg ha hv
    rw [hl]
    exact ⟨_, rfl⟩
  · rw [heq]
    exact Near.Boundary.observeChecked_matchesOrGas code.codeOf ctx raw result
      (reference ctx raw budget (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)))
      (ReceiptSimulation.matchesOrGas_machineBelow hsim)

end WNear.Skeleton.CanonicalReceiptSimulation
