import Model.SyncGovernance

namespace SputnikDAO2

theorem replace_policy_refunds_old_bond (state : SyncGovernanceState)
    (newPolicy : GovernanceParameters) (proposer : String) :
    executeSyncGovernance state (.replacePolicy newPolicy) proposer =
      some ⟨{ state with policy := newPolicy, locked := state.locked - state.policy.proposalBond },
        ⟨proposer, state.policy.proposalBond⟩, false⟩ := by
  rfl

theorem patch_parameters_refunds_old_bond (state : SyncGovernanceState)
    (patch : GovernanceParameterPatch) (proposer : String) :
    executeSyncGovernance state (.updateParameters patch) proposer =
      some ⟨{ state with policy := applyParameterPatch state.policy patch, locked := state.locked - state.policy.proposalBond },
        ⟨proposer, state.policy.proposalBond⟩, false⟩ := by
  rfl

theorem patch_none_preserves_all_parameters (old : GovernanceParameters) :
    applyParameterPatch old ⟨none, none, none, none⟩ = old := by
  cases old <;> rfl

theorem patch_only_bond_preserves_other_parameters
    (old : GovernanceParameters) (bond : Nat) :
    applyParameterPatch old ⟨some bond, none, none, none⟩ =
      { old with proposalBond := bond } := by
  cases old <;> rfl

theorem first_staking_execution_succeeds (state : SyncGovernanceState)
    (account proposer : String) (h : state.staking = none) :
    executeSyncGovernance state (.setStaking account) proposer =
      some ⟨{ state with staking := some account, locked := state.locked - state.policy.proposalBond },
        ⟨proposer, state.policy.proposalBond⟩, false⟩ := by
  simp [executeSyncGovernance, h]

theorem later_staking_execution_aborts (state : SyncGovernanceState)
    (account existing proposer : String) (h : state.staking = some existing) :
    executeSyncGovernance state (.setStaking account) proposer = none := by
  simp [executeSyncGovernance, h]

theorem successful_sync_action_never_schedules_callback
    (state : SyncGovernanceState) (action : SyncGovernanceAction)
    (proposer : String) (outcome : SyncGovernanceOutcome)
    (h : executeSyncGovernance state action proposer = some outcome) :
    outcome.callbackScheduled = false := by
  cases action with
  | replacePolicy policy =>
      simp [executeSyncGovernance] at h
      cases h
      rfl
  | updateParameters patch =>
      simp [executeSyncGovernance] at h
      cases h
      rfl
  | setStaking account =>
      cases hs : state.staking with
      | none =>
          simp [executeSyncGovernance, hs] at h
          cases h
          rfl
      | some existing =>
          simp [executeSyncGovernance, hs] at h

theorem replacement_can_store_legacy_policy {α : Type}
    (old : α) (council : List String) :
    executePolicyStorageAction (some (.current old))
      (.replace (.default council)) = .ok (.default council) := by
  rfl

theorem validated_replacement_rejects_legacy {α : Type}
    (stored : Option (StoredPolicy α)) (council : List String) :
    executeValidatedPolicyReplacement stored (.default council) = none := by
  rfl

theorem validated_replacement_preserves_current {α : Type}
    (old replacement : α) :
    executeValidatedPolicyReplacement (some (.current old))
      (.current replacement) = some (.current replacement) := by
  rfl

theorem legacy_replacement_breaks_next_policy_read {α : Type}
    (old : α) (council : List String) :
    (executePolicyStorageAction (some (.current old))
      (.replace (.default council))).bind
      (fun stored => readPolicy (some stored)) = .error .legacy := by
  rfl

theorem legacy_replacement_blocks_next_policy_action {α : Type}
    (old replacement : α) (council : List String) :
    (executePolicyStorageAction (some (.current old))
      (.replace (.default council))).bind
      (fun stored => executePolicyStorageAction (some stored)
        (.replace (.current replacement))) = .error .legacy := by
  rfl

theorem mutation_preserves_current_policy {α : Type}
    (old : α) (change : α → α) :
    executePolicyStorageAction (some (.current old)) (.mutate change) =
      .ok (.current (change old)) := by
  rfl

theorem validated_policy_action_preserves_current {α : Type}
    (old : α) (action : PolicyStorageAction α)
    (result : StoredPolicy α)
    (h : executeValidatedPolicyAction (.current old) action = some result) :
    ∃ next : α, result = .current next := by
  cases action with
  | replace replacement =>
      cases replacement with
      | default council =>
          simp [executeValidatedPolicyAction,
            executeValidatedPolicyReplacement, validPolicyReplacement] at h
      | current next =>
          simp [executeValidatedPolicyAction,
            executeValidatedPolicyReplacement, validPolicyReplacement,
            executePolicyStorageAction, readPolicy] at h
          cases h
          exact ⟨next, rfl⟩
  | mutate change =>
      simp [executeValidatedPolicyAction,
        executePolicyStorageAction, readPolicy] at h
      cases h
      exact ⟨change old, rfl⟩

theorem validated_policy_trace_preserves_current {α : Type}
    (old : α) (actions : List (PolicyStorageAction α))
    (result : StoredPolicy α)
    (h : executeValidatedPolicyTrace (.current old) actions = some result) :
    ∃ next : α, result = .current next := by
  induction actions generalizing old with
  | nil =>
      simp [executeValidatedPolicyTrace] at h
      exact ⟨old, h.symm⟩
  | cons action rest ih =>
      simp only [executeValidatedPolicyTrace] at h
      cases hstep : executeValidatedPolicyAction (.current old) action with
      | none => simp [hstep] at h
      | some intermediate =>
          obtain ⟨next, hcurrent⟩ :=
            validated_policy_action_preserves_current old action intermediate hstep
          subst intermediate
          simp [hstep] at h
          exact ih next h

end SputnikDAO2
