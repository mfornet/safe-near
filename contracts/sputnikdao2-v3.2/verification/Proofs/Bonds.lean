import Model.Bonds

namespace SputnikDAO2

theorem remove_first_claim_length (claims : List BondClaim)
    (account : String) (found : BondClaim) (remaining : List BondClaim)
    (h : removeFirstClaim claims account = some (found, remaining)) :
    remaining.length + 1 = claims.length := by
  induction claims generalizing found remaining with
  | nil => simp [removeFirstClaim] at h
  | cons claim rest ih =>
      by_cases hmatch : claim.account = account
      · simp [removeFirstClaim, hmatch] at h
        rcases h with ⟨_, hremaining⟩
        subst remaining
        simp
      · cases hrec : removeFirstClaim rest account with
        | none => simp [removeFirstClaim, hmatch, hrec] at h
        | some pair =>
            obtain ⟨inner, tail⟩ := pair
            simp [removeFirstClaim, hmatch, hrec] at h
            rcases h with ⟨_, hremaining⟩
            subst remaining
            have hlen := ih inner tail hrec
            simp
            omega

theorem claim_requires_exact_bond (state : BountyBondState) (account : String)
    (now duration maxDeadline times policyBond attached : Nat)
    (h : attached ≠ policyBond) :
    bountyClaim state account now duration maxDeadline times
      policyBond attached = none := by
  simp [bountyClaim, h]

theorem claim_adds_one_when_under_cap (state : BountyBondState)
    (account : String) (now duration maxDeadline times bond : Nat)
    (hcount : state.claimCount < times) (hdeadline : duration ≤ maxDeadline) :
    ∃ next,
      bountyClaim state account now duration maxDeadline times bond bond =
        some next ∧
      next.claimCount = state.claimCount + 1 ∧
      next.locked = min (state.locked + bond) maxU128 ∧
      next.claims = state.claims ++ [⟨account, now, duration, false, bond⟩] := by
  refine ⟨⟨state.claims ++ [⟨account, now, duration, false, bond⟩],
    state.claimCount + 1, min (state.locked + bond) maxU128⟩, ?_, rfl, rfl, rfl⟩
  simp [bountyClaim, Nat.not_le.mpr hcount, Nat.not_lt.mpr hdeadline]

theorem claim_preserves_count_length (state : BountyBondState)
    (account : String) (now duration maxDeadline times bond : Nat)
    (hcoherent : state.claimCount = state.claims.length)
    (hcount : state.claimCount < times) (hdeadline : duration ≤ maxDeadline) :
    ∃ next,
      bountyClaim state account now duration maxDeadline times bond bond =
        some next ∧ next.claimCount = next.claims.length := by
  obtain ⟨next, hstep, hnext, _, hclaims⟩ :=
    claim_adds_one_when_under_cap state account now duration
      maxDeadline times bond hcount hdeadline
  refine ⟨next, hstep, ?_⟩
  simp [hnext, hclaims, hcoherent]

theorem timely_giveup_refunds_current_bond (state : BountyBondState)
    (account : String) (found : BondClaim) (remaining : List BondClaim)
    (now forgiveness currentBond : Nat)
    (hremove : removeFirstClaim state.claims account = some (found, remaining))
    (hstart : found.start ≤ now)
    (hcount : 0 < state.claimCount)
    (hwithin : now - found.start ≤ forgiveness)
    (hlocked : currentBond ≤ state.locked)
    (hcoherent : state.claimCount = state.claims.length) :
    ∃ next,
      bountyGiveup state account now forgiveness currentBond =
        some (next, some currentBond) ∧
      next.locked + currentBond = state.locked ∧
      next.claimCount = next.claims.length := by
  let next : BountyBondState :=
    ⟨remaining, state.claimCount - 1, state.locked - currentBond⟩
  have hstep : bountyGiveup state account now forgiveness currentBond =
      some (next, some currentBond) := by
    simp [bountyGiveup, hremove, Nat.not_lt.mpr hstart,
      Nat.ne_of_gt hcount, Nat.not_lt.mpr hwithin, next]
  have hlen := remove_first_claim_length state.claims account found remaining hremove
  refine ⟨next, hstep, ?_, ?_⟩
  · simp only [next]
    omega
  · simp only [next]
    omega

theorem late_giveup_keeps_locked_amount (state : BountyBondState)
    (account : String) (found : BondClaim) (remaining : List BondClaim)
    (now forgiveness currentBond : Nat)
    (hremove : removeFirstClaim state.claims account = some (found, remaining))
    (hstart : found.start ≤ now)
    (hcount : 0 < state.claimCount)
    (hlate : forgiveness < now - found.start)
    (hcoherent : state.claimCount = state.claims.length) :
    ∃ next,
      bountyGiveup state account now forgiveness currentBond =
        some (next, none) ∧
      next.locked = state.locked ∧
      next.claimCount = next.claims.length := by
  let next : BountyBondState :=
    ⟨remaining, state.claimCount - 1, state.locked⟩
  have hstep : bountyGiveup state account now forgiveness currentBond =
      some (next, none) := by
    simp [bountyGiveup, hremove, Nat.not_lt.mpr hstart,
      Nat.ne_of_gt hcount, hlate, next]
  have hlen := remove_first_claim_length state.claims account found remaining hremove
  refine ⟨next, hstep, rfl, ?_⟩
  simp only [next]
  omega

theorem changed_bond_changes_refund :
    bountyGiveup
      ⟨[⟨"alice.near", 100, 10, false, 10⟩], 1, 10⟩
      "alice.near" 101 10 5 =
      some (⟨[], 0, 5⟩, some 5) := by
  decide

theorem late_giveup_keeps_lock :
    bountyGiveup
      ⟨[⟨"alice.near", 100, 10, false, 10⟩], 1, 10⟩
      "alice.near" 111 10 10 =
      some (⟨[], 0, 10⟩, none) := by
  decide

theorem future_start_aborts_on_checked_subtraction :
    bountyGiveup
      ⟨[⟨"alice.near", 100, 10, false, 10⟩], 1, 10⟩
      "alice.near" 99 10 10 = none := by
  decide

end SputnikDAO2
