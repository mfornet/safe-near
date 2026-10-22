import Model.MultiVote

namespace SputnikDAO2

theorem token_weighted_role_uses_user_weight (role : StatusRole) (weight : Nat)
    (h : role.weightKind = .token) :
    roleVoteAmount role weight = weight := by simp [roleVoteAmount, h]

theorem role_weighted_role_uses_one (role : StatusRole) (weight : Nat)
    (h : role.weightKind = .role) :
    roleVoteAmount role weight = 1 := by simp [roleVoteAmount, h]

theorem selected_approval_count_exact (role next : StatusRole) (weight : Nat)
    (h : countSelectedRole role .approve weight = some next) :
    next.approvals = role.approvals + roleVoteAmount role weight ∧
    next.rejections = role.rejections ∧ next.removals = role.removals := by
  simp [countSelectedRole] at h
  rcases h with ⟨_, heq⟩
  cases heq
  simp

theorem selected_approval_overflow_aborts (role : StatusRole) (weight : Nat)
    (h : maxU128 < role.approvals + roleVoteAmount role weight) :
    countSelectedRole role .approve weight = none := by
  simp [countSelectedRole, h]

theorem countSelectedRoles_length (roles next : List StatusRole)
    (choice : VoteChoice) (weight : Nat)
    (h : countSelectedRoles roles choice weight = some next) :
    next.length = roles.length := by
  induction roles generalizing next with
  | nil => simp [countSelectedRoles] at h; cases h; rfl
  | cons role rest ih =>
      simp only [countSelectedRoles] at h
      cases hc : countSelectedRole role choice weight with
      | none => simp [hc] at h
      | some counted =>
          simp [hc] at h
          cases ht : countSelectedRoles rest choice weight with
          | none => simp [ht] at h
          | some tail =>
              simp [ht] at h
              cases h
              simp [ih tail ht]

theorem multiVoteStep_requires_in_progress (state : MultiVoteState)
    (account : String) (choice : VoteChoice)
    (weight submission period now supply : Nat)
    (h : state.status ≠ .inProgress) :
    multiVoteStep state account choice weight submission period now supply = none := by
  simp [multiVoteStep, h]

theorem multiVoteStep_rejects_duplicate (state : MultiVoteState)
    (account : String) (choice : VoteChoice)
    (weight submission period now supply : Nat)
    (h : account ∈ state.voters) :
    multiVoteStep state account choice weight submission period now supply = none := by
  by_cases hs : state.status = .inProgress
  · simp [multiVoteStep, hs, h]
  · simp [multiVoteStep, hs]

theorem multiVoteStep_time_overflow (state : MultiVoteState)
    (account : String) (choice : VoteChoice)
    (weight submission period now supply : Nat)
    (h : maxU64 < submission + period) :
    multiVoteStep state account choice weight submission period now supply = none := by
  simp [multiVoteStep, h]

theorem multiVoteStep_adds_voter (state next : MultiVoteState)
    (account : String) (choice : VoteChoice)
    (weight submission period now supply : Nat)
    (h : multiVoteStep state account choice weight submission period now supply = some next) :
    account ∈ next.voters := by
  unfold multiVoteStep at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Option.bind_eq_bind] at h
  cases hc : countSelectedRoles state.selectedRoles choice weight with
  | none => simp [hc] at h
  | some counted =>
      simp [hc] at h
      cases hs : proposalStatusChecked .inProgress submission period now supply counted with
      | none => simp [hs] at h
      | some status =>
          simp [hs] at h
          cases h
          simp

theorem multiVoteStep_prevents_second_vote (state next : MultiVoteState)
    (account : String) (first second : VoteChoice)
    (weight submission period now supply : Nat)
    (h : multiVoteStep state account first weight submission period now supply = some next) :
    multiVoteStep next account second weight submission period now supply = none := by
  exact multiVoteStep_rejects_duplicate next account second weight submission period now supply
    (multiVoteStep_adds_voter state next account first weight submission period now supply h)

theorem multiVoteStep_selected_role_count (state next : MultiVoteState)
    (account : String) (choice : VoteChoice)
    (weight submission period now supply : Nat)
    (h : multiVoteStep state account choice weight submission period now supply = some next) :
    next.selectedRoles.length = state.selectedRoles.length := by
  unfold multiVoteStep at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases hc : countSelectedRoles state.selectedRoles choice weight with
  | none => simp [hc] at h
  | some counted =>
      simp [hc] at h
      cases hs : proposalStatusChecked .inProgress submission period now supply counted with
      | none => simp [hs] at h
      | some status =>
          simp [hs] at h
          cases h
          exact countSelectedRoles_length state.selectedRoles counted choice weight hc

def oneRoleFixture : StatusRole :=
  ⟨.group 1, .role, 0, .weight 1, 0, 0, 0⟩

theorem vote_after_expiry_is_counted_then_marked_expired :
    multiVoteStep ⟨.inProgress, [], [oneRoleFixture]⟩
      "alice.near" .approve 7 0 1 2 0 =
      some ⟨.expired, ["alice.near"],
        [⟨.group 1, .role, 0, .weight 1, 1, 0, 0⟩]⟩ := by
  decide

theorem vote_ratio_overflow_aborts_after_count :
    multiVoteStep
      ⟨.inProgress, [], [⟨.member, .token, 0, .ratio 1 1, 0, 0, 0⟩]⟩
      "alice.near" .approve 1 0 1 0 maxU128 = none := by
  decide

theorem expired_vote_counts_before_skipping_unsafe_ratio :
    multiVoteStep
      ⟨.inProgress, [], [⟨.member, .token, 0, .ratio 1 1, 0, 0, 0⟩]⟩
      "alice.near" .approve 1 0 0 1 maxU128 =
      some ⟨.expired, ["alice.near"],
        [⟨.member, .token, 0, .ratio 1 1, 1, 0, 0⟩]⟩ := by
  decide

end SputnikDAO2
