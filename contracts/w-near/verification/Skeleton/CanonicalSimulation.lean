import Skeleton.CanonicalReady

/-! Whole-body budget replay over arbitrary canonical trie states. -/
namespace WNear.Skeleton.CanonicalSimulation
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget MeteredHostBudget NearInterface
open MeteredHosts BudgetSimulation FunctionalInvariant

/-- One-step replay uses original canonical WF and node-zero evidence to
supply actual fresh/replacement readiness, independently of paid gas. -/
theorem stepSimulation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw) :
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
        exact CanonicalReady.storageReady_allKeyLimits ctx raw store (hr.beforeWrite (by omega))
          (hr.register (by omega) (by omega)) hwf hpages hnodes hproof)
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

/-- Complete actual body runs match or the low run aborts for protocol gas;
structural fuel exhaustion is excluded without any empty-base restriction. -/
theorem runSimulation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw)
    (fuel : Nat) (small large : Machine)
    (hrel : Related (SimulationRelation ctx raw limits) small large)
    (hbound : Progress.rank large ≤ fuel) :
    MatchesOrGas (SimulationRelation ctx raw limits)
        (runMetered ctx.protocol.wasm fuel small) (runMetered ctx.protocol.wasm fuel large) ∧
      (runMetered ctx.protocol.wasm fuel small).2 ≠ some (.executionIssue .fuelExhausted) := by
  have hshape := related_shape ctx raw limits hrel
  exact run_simulation_no_fuel ctx.protocol.wasm (SimulationRelation ctx raw limits)
    (stepSimulation ctx raw limits hwf hpages hnodes hproof)
    (Shape ctx.protocol limits) (shape_advanceInvariant ctx.protocol limits) (shape_logsMonotone ctx.protocol limits)
    fuel small large hrel hshape (Progress.run_not_fuel ctx.protocol limits fuel large hshape hbound)

/-- Initialized whole-body replay keeps the same guest-visible context and
allows arbitrary internal reference budget over arbitrary canonical storage. -/
theorem initialized_runSimulation (ctx : Context) (raw : Storage) (limits : ExecLimits)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : CanonicalReady.ProofAccepted ctx raw)
    (budget fuel : Nat) (hfuel : 16 ≤ fuel) :
    let small := phaseMachine (initializedStore ctx.protocol (origin ctx raw) (preparedData ctx.protocol)) limits 0 0
    let large := phaseMachine (initializedStore ctx.protocol (enlargeHost (origin ctx raw) budget) (preparedData ctx.protocol)) limits 0 0
    MatchesOrGas (SimulationRelation ctx raw limits)
        (runMetered ctx.protocol.wasm fuel small) (runMetered ctx.protocol.wasm fuel large) ∧
      (runMetered ctx.protocol.wasm fuel small).2 ≠ some (.executionIssue .fuelExhausted) := by
  exact runSimulation ctx raw limits hwf hpages hnodes hproof fuel _ _
    (initial_related ctx raw limits budget) (by change 16 ≤ fuel; exact hfuel)

end WNear.Skeleton.CanonicalSimulation
