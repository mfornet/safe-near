import Model.AddBountyExecution
import Model.BountyStorage

namespace SputnikDAO2

theorem add_bounty_overflow_aborts (state : AddBountyState)
    (bounty : BountyImage) (bond : Nat) (proposer : String)
    (h : state.lastId ≥ maxU64) :
    executeAddBounty state bounty bond proposer = none := by
  simp [executeAddBounty, h]

theorem add_bounty_returns_old_id_and_refund (state : AddBountyState)
    (bounty : BountyImage) (bond : Nat) (proposer : String)
    (h : state.lastId < maxU64) :
    (executeAddBounty state bounty bond proposer).map
      (fun result =>
        (result.createdId, result.state.lastId, result.refund,
          result.callbackScheduled)) =
      some (state.lastId, state.lastId + 1,
        ⟨proposer, bond⟩, false) := by
  simp [executeAddBounty, Nat.not_le.mpr h]

theorem add_bounty_stores_at_old_id (state : AddBountyState)
    (bounty : BountyImage) (bond : Nat) (proposer : String)
    (h : state.lastId < maxU64) :
    (executeAddBounty state bounty bond proposer).bind
      (fun result => bountyAt result.state.bounties state.lastId) =
      some bounty := by
  simp [executeAddBounty, Nat.not_le.mpr h]
  induction state.bounties with
  | nil => simp [setBounty, bountyAt]
  | cons pair rest ih =>
      obtain ⟨id, old⟩ := pair
      by_cases heq : id = state.lastId
      · simp [setBounty, bountyAt, heq]
      · simp [setBounty, bountyAt, heq, ih]

theorem add_bounty_preserves_all_claim_counts (state : AddBountyState)
    (bounty : BountyImage) (bond : Nat) (proposer : String)
    (h : state.lastId < maxU64) (id : Nat) :
    (executeAddBounty state bounty bond proposer).map
      (fun result => result.state.claimCounts id) =
      some (state.claimCounts id) := by
  simp [executeAddBounty, Nat.not_le.mpr h]

theorem zero_times_and_unparsed_token_are_accepted
    (state : AddBountyState) (description token : String)
    (amount deadline bond : Nat) (proposer : String)
    (h : state.lastId < maxU64) :
    (executeAddBounty state
      ⟨description, token, amount, 0, deadline⟩ bond proposer).map
      (fun result => result.createdId) = some state.lastId := by
  simp [executeAddBounty, Nat.not_le.mpr h]

theorem add_bounty_preserves_input_widths
    (state : AddBountyState) (bounty : BountyImage)
    (bond : Nat) (proposer : String)
    (h : state.lastId < maxU64) (hvalid : validBountyImage bounty) :
    (executeAddBounty state bounty bond proposer).bind
      (fun result => bountyAt result.state.bounties state.lastId) =
      some bounty ∧ validBountyImage bounty := by
  exact ⟨add_bounty_stores_at_old_id state bounty bond proposer h, hvalid⟩

theorem zero_times_bounty_cannot_be_claimed
    (storage : BountyStorageState) (account : String)
    (id now deadline maxDeadline policyBond attached : Nat) :
    addStoredClaim storage account id now deadline maxDeadline 0
      policyBond attached = none := by
  simp [addStoredClaim]

end SputnikDAO2
