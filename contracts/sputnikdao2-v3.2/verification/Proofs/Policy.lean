import Model.Policy

namespace SputnikDAO2

theorem weight_capped (amount total : Nat) :
    toWeight (.weight amount) total ≤ total := by
  exact Nat.min_le_right _ _

theorem ratio_capped (numerator denominator total : Nat) :
    toWeight (.ratio numerator denominator) total ≤ total := by
  exact Nat.min_le_right _ _

theorem zero_total_ratio (numerator denominator : Nat) :
    toWeight (.ratio numerator denominator) 0 = 0 := by
  simp [toWeight]

theorem quorum_floor (quorum total : Nat) (choice : WeightOrRatio) :
    quorum ≤ voteThreshold quorum choice total := by
  exact Nat.le_max_left _ _

theorem quorum_above_supply_blocks_attainable_votes
    (quorum total : Nat) (choice : WeightOrRatio)
    (h : total < quorum) (votes : Nat) (hv : votes ≤ total) :
    votes < voteThreshold quorum choice total := by
  simp only [voteThreshold]
  omega

theorem default_ratio_two : toWeight (.ratio 1 2) 2 = 2 := by
  decide

theorem default_ratio_five : toWeight (.ratio 1 2) 5 = 3 := by
  decide

theorem zero_ratio_nonempty (total : Nat) (h : 0 < total) :
    toWeight (.ratio 0 1) total = 1 := by
  simp only [toWeight, Nat.zero_mul, Nat.zero_div, Nat.zero_add]
  omega

theorem approval_wins_tie (threshold approvals rejections removals : Nat)
    (h : threshold ≤ approvals) :
    decideRole threshold approvals rejections removals = .approved := by
  simp [decideRole, h]

theorem rejection_wins_remove (threshold approvals rejections removals : Nat)
    (ha : approvals < threshold) (hr : threshold ≤ rejections) :
    decideRole threshold approvals rejections removals = .rejected := by
  simp [decideRole, Nat.not_le.mpr ha, hr]

theorem zero_threshold_approves_without_votes :
    decideRole 0 0 0 0 = .approved := by
  decide

theorem role_order_can_change_result :
    firstDecisive [.approved, .rejected] = .approved ∧
    firstDecisive [.rejected, .approved] = .rejected := by
  decide

theorem first_decisive_consistent (decision : Decision)
    (hdec : decision ≠ .inProgress) (roles : List Decision)
    (hagree : ∀ role ∈ roles, role = .inProgress ∨ role = decision)
    (hpresent : decision ∈ roles) :
    firstDecisive roles = decision := by
  induction roles with
  | nil => simp at hpresent
  | cons head tail ih =>
      have hhead := hagree head (by simp)
      rcases hhead with hhead | hhead
      · subst head
        have htail : ∀ role ∈ tail, role = .inProgress ∨ role = decision := by
          intro role hrole
          exact hagree role (by simp [hrole])
        have htailPresent : decision ∈ tail := by
          simpa [hdec] using hpresent
        simpa [firstDecisive] using ih htail htailPresent
      · subst head
        simp [firstDecisive]

theorem expiration_is_strict_at_boundary (submission period : Nat) :
    expired submission period (submission + period) = false := by
  simp [expired]

theorem expiration_after_boundary (submission period now : Nat)
    (h : submission + period < now) :
    expired submission period now = true := by
  simp [expired, h]

end SputnikDAO2
