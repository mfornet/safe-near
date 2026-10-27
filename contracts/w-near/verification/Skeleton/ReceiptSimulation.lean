import Skeleton.StartupSimulation
import Skeleton.Fuel
import NearRuntime.BudgetObservation

/-!
# Actual receipt observation under an enlarged internal gas budget

The reference uses the original guest context and pays actual loading and entry
activation. It is an auxiliary execution, not an assumed model outcome. Public
receipt checking preserves exact matching or gas abort with rollback/prefix logs.
-/
namespace WNear.Skeleton.ReceiptSimulation
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget NearInterface
open FunctionalInvariant StartupSimulation

/-- Public observation of the auxiliary body after its actual startup charges,
using exactly the default fuel of the original attempt. -/
def referenceObservation (ctx : Context) (raw : Storage) (budget : Nat) : Observation :=
  let result := reference ctx raw budget (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx))
  Near.Boundary.observeChecked code.codeOf ctx raw
    (outcomeOfExecution (Near.Boundary.toVMContext ctx) raw result.1 result.2)

/-- Drop the closed functional invariant only after obtaining actual replay. -/
theorem matchesOrGas_machineBelow {ctx : Context} {raw : Storage} {limits : ExecLimits}
    {low high : Machine × Option FunctionCallError}
    (h : MatchesOrGas (SimulationRelation ctx raw limits) low high) :
    MatchesOrGas MachineBelow low high := by
  rcases h with ⟨hr, he⟩ | hg
  · exact Or.inl ⟨hr.state.1.related, he⟩
  · exact Or.inr hg

/-- The actual default-fuel receipt execution matches the auxiliary observation
or aborts out of gas, rolls back, and retains a prefix of its logs. No model
adequacy or whole-run execution property is a premise. -/
theorem execOn_replay (ctx : Context) (raw : Storage) (budget : Nat)
    (hmethod : ctx.method = "save")
    (hwf : ctx.WF raw.toFinset) (hpositive : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hminmax : ctx.protocol.wasm.limits.initialMemoryPages ≤ ctx.protocol.wasm.limits.maxMemoryPages)
    (hmax : ctx.protocol.wasm.limits.maxMemoryPages ≤ 65536)
    (htypes : ∀ n, ctx.protocol.wasm.limits.maxTypesPerContract = some n → 4 ≤ n)
    (hfunctions : ∀ n, ctx.protocol.wasm.limits.maxFunctionsNumberPerContract = some n → 5 ≤ n)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hproof : recordedStorageError (origin ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none) :
    let observed := Near.Boundary.execOn code raw ctx
    observed = referenceObservation ctx raw budget ∨
      (observed.outcome = .error .outOfGas ∧ RolledBack ctx raw.toFinset observed ∧
        observed.logs <+: (referenceObservation ctx raw budget).logs) := by
  have hexec := Near.Boundary.execOn_observeChecked code ctx raw rfl
  change Near.Boundary.execOn code raw ctx = Near.Boundary.observeChecked code.codeOf ctx raw
    (runAttempt ctx.protocol module 0 ctx.method (Near.Boundary.toVMContext ctx) raw
      (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx))) at hexec
  rw [hmethod] at hexec
  change Near.Boundary.execOn code raw ctx = referenceObservation ctx raw budget ∨ _
  rw [hexec]
  have hr := runAttempt_replay ctx raw budget
    (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)) hwf hpositive hminmax hmax htypes hfunctions
    hentries hselected hproof (fuelFor_save _ _)
  rcases hr with hstartup | ⟨result, heq, hsim, _⟩
  · right
    obtain ⟨error, hg, ha, hl, hv⟩ := hstartup
    apply Near.Boundary.observeChecked_protocolGas code.codeOf ctx raw _ error _ hg ha hv
    rw [hl]
    exact ⟨_, rfl⟩
  · rw [heq]
    exact Near.Boundary.observeChecked_matchesOrGas code.codeOf ctx raw result
      (reference ctx raw budget (fuelFor ctx.protocol module (Near.Boundary.toVMContext ctx)))
      (matchesOrGas_machineBelow hsim)

end WNear.Skeleton.ReceiptSimulation
