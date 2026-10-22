import Model.Status

namespace SputnikDAO2

theorem proposal_status_rejects_terminal (original : ProposalStatus)
    (submission period now totalSupply : Nat) (roles : List StatusRole)
    (h1 : original ≠ .inProgress) (h2 : original ≠ .failed) :
    proposalStatusForRoles original submission period now totalSupply roles = none := by
  simp [proposalStatusForRoles, h1, h2]

theorem expiration_precedes_roles (original : ProposalStatus)
    (submission period now totalSupply : Nat) (roles : List StatusRole)
    (hstatus : original = .inProgress ∨ original = .failed)
    (hexpired : submission + period < now) :
    proposalStatusForRoles original submission period now totalSupply roles =
      some .expired := by
  rcases hstatus with h | h <;> subst original <;>
    simp [proposalStatusForRoles, expired, hexpired]

theorem everyone_cannot_decide (role : StatusRole) (supply : Nat)
    (h : role.kind = .everyone) :
    roleDecision role supply = .inProgress := by
  simp [roleDecision, h]

theorem no_roles_preserves_failed (submission period now supply : Nat)
    (h : now ≤ submission + period) :
    proposalStatusForRoles .failed submission period now supply [] =
      some .failed := by
  simp [proposalStatusForRoles, expired, Nat.not_lt.mpr h, firstDecisive]

theorem empty_group_zero_quorum_approves :
    roleDecision
      ⟨.group 0, .role, 0, .ratio 1 2, 0, 0, 0⟩ 0 = .approved := by
  decide

theorem conflicting_role_order_changes_status :
    let approveRole : StatusRole :=
      ⟨.group 1, .role, 1, .weight 1, 1, 0, 0⟩
    let rejectRole : StatusRole :=
      ⟨.group 1, .role, 1, .weight 1, 0, 1, 0⟩
    proposalStatusForRoles .inProgress 0 10 0 0
      [approveRole, rejectRole] = some .approved ∧
    proposalStatusForRoles .inProgress 0 10 0 0
      [rejectRole, approveRole] = some .rejected := by
  decide

end SputnikDAO2
