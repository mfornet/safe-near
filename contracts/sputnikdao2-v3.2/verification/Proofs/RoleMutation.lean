import Model.RoleMutation

namespace SputnikDAO2

theorem replace_first_duplicate_only (first second replacement : MutableRole)
    (rest : List MutableRole) (h : first.name = replacement.name) :
    replaceOrAppendRole (first :: second :: rest) replacement =
      (replacement :: second :: rest, .updated) := by
  simp [replaceOrAppendRole, h]

theorem remove_first_duplicate_only (first second : MutableRole)
    (rest : List MutableRole) :
    removeFirstRole (first :: second :: rest) first.name =
      (second :: rest, .none) := by
  simp [removeFirstRole]

theorem wrong_kind_first_duplicate_blocks_later_group
    (first second : MutableRole) (rest : List MutableRole)
    (member : String) (_hname : first.name = second.name)
    (hshape : first.shape = .everyone) :
    changeFirstMember (first :: second :: rest) first.name member true =
      (first :: second :: rest, .wrongKind) := by
  simp [changeFirstMember, hshape]

theorem missing_role_mutation_keeps_policy_and_refunds
    (policy : MutablePolicyImage) (locked : Nat)
    (name proposer : String)
    (h : ∀ role ∈ policy.roles, role.name ≠ name) :
    executeRoleMutation policy locked (.remove name) proposer =
      ⟨policy, locked - policy.proposalBond,
        ⟨proposer, policy.proposalBond⟩, .missing, false⟩ := by
  have aux : ∀ roles : List MutableRole,
      (∀ role ∈ roles, role.name ≠ name) →
      removeFirstRole roles name = (roles, .missing) := by
    intro roles
    induction roles with
    | nil => intro _; rfl
    | cons role rest ih =>
        intro hn
        have hr : role.name ≠ name := hn role (by simp)
        have ht : ∀ r ∈ rest, r.name ≠ name := by
          intro r hh
          exact hn r (by simp [hh])
        simp [removeFirstRole, hr, ih ht]
  simp [executeRoleMutation, mutatePolicy, aux policy.roles h]

theorem role_mutation_always_refunds_old_bond
    (policy : MutablePolicyImage) (locked : Nat)
    (action : RoleMutationAction) (proposer : String) :
    (executeRoleMutation policy locked action proposer).refund =
      ⟨proposer, policy.proposalBond⟩ ∧
    (executeRoleMutation policy locked action proposer).locked =
      locked - policy.proposalBond ∧
    (executeRoleMutation policy locked action proposer).callbackScheduled = false := by
  simp [executeRoleMutation]

end SputnikDAO2
