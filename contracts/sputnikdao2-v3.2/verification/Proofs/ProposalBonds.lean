import Model.ProposalBonds

namespace SputnikDAO2

theorem ordinary_bond_return (locked : Nat) (policy : BondPolicyAmounts)
    (proposer : String) :
    returnProposalBonds locked policy proposer false =
      ⟨locked - policy.proposalBond, [],
        ⟨proposer, policy.proposalBond⟩⟩ := by
  rfl

theorem bounty_done_returns_two_promises (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String) :
    returnProposalBonds locked policy proposer true =
      ⟨(locked - policy.bountyBond) - policy.proposalBond,
        [⟨proposer, policy.bountyBond⟩],
        ⟨proposer, policy.proposalBond⟩⟩ := by
  rfl

theorem bond_refund_total_matches_current_policy (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (isBountyDone : Bool) :
    totalScheduledRefund
      (returnProposalBonds locked policy proposer isBountyDone) =
      policy.proposalBond + (if isBountyDone then policy.bountyBond else 0) := by
  cases isBountyDone <;>
    simp [returnProposalBonds, totalScheduledRefund, Nat.add_comm]

theorem ordinary_lock_drops_by_bond_when_sufficient (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (h : policy.proposalBond ≤ locked) :
    (returnProposalBonds locked policy proposer false).lockedAfter +
      policy.proposalBond = locked := by
  simp [returnProposalBonds]
  omega

theorem bounty_lock_drops_by_both_when_sufficient (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (h : policy.bountyBond + policy.proposalBond ≤ locked) :
    (returnProposalBonds locked policy proposer true).lockedAfter +
      policy.bountyBond + policy.proposalBond = locked := by
  simp [returnProposalBonds]
  omega

theorem scheduled_refund_can_exceed_locked_counter :
    let result := returnProposalBonds 1 ⟨2, 2⟩ "alice.near" true
    result.lockedAfter = 0 ∧ totalScheduledRefund result = 4 := by
  decide

theorem current_bond_can_differ_from_historical_lock :
    returnProposalBonds 10 ⟨5, 0⟩ "alice.near" false =
      ⟨5, [], ⟨"alice.near", 5⟩⟩ := by
  decide

end SputnikDAO2
