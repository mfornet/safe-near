import Model.BountyStorage

namespace SputnikDAO2

theorem account_claim_count_append_matching
    (claims : List StoredBountyClaim) (bountyId now deadline bond : Nat) :
    accountClaimCount
      (claims ++ [⟨bountyId, now, deadline, false, bond⟩]) bountyId =
      accountClaimCount claims bountyId + 1 := by
  simp [accountClaimCount, List.filter_append]

theorem account_claim_count_append_other
    (claims : List StoredBountyClaim)
    (bountyId otherBounty now deadline bond : Nat)
    (hother : otherBounty ≠ bountyId) :
    accountClaimCount
      (claims ++ [⟨bountyId, now, deadline, false, bond⟩]) otherBounty =
      accountClaimCount claims otherBounty := by
  simp [accountClaimCount, List.filter_append, Ne.symm hother]

theorem observed_other_accounts_unchanged
    (state : BountyStorageState) (account : String)
    (replacement : Option (List StoredBountyClaim)) (others : List String)
    (bountyId : Nat) (hnot : account ∉ others) :
    observedBountyCount
      { state with claimers := fun key =>
          if key == account then replacement else state.claimers key }
      others bountyId =
    observedBountyCount state others bountyId := by
  induction others with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ≠ account := by
        intro heq
        exact hnot (by simp [heq])
      have htail : account ∉ tail := by
        intro hmem
        exact hnot (by simp [hmem])
      simp only [observedBountyCount, List.map_cons,
        List.sum_cons] at *
      simp [hhead]
      simpa using ih htail

theorem observed_count_unchanged_when_local_same
    (state : BountyStorageState) (account : String)
    (replacement : Option (List StoredBountyClaim))
    (others : List String) (bountyId : Nat)
    (hnot : account ∉ others)
    (hlocal : accountClaimCount (replacement.getD []) bountyId =
      accountClaimCount ((state.claimers account).getD []) bountyId) :
    observedBountyCount
      { state with claimers := fun key =>
          if key == account then replacement else state.claimers key }
      (account :: others) bountyId =
    observedBountyCount state (account :: others) bountyId := by
  have htail := observed_other_accounts_unchanged state account
    replacement others bountyId hnot
  simp only [observedBountyCount, List.map_cons, List.sum_cons] at ⊢
  simp [hlocal]
  simp only [observedBountyCount] at htail
  simp at htail
  rw [htail]

theorem observed_count_adds_one_for_enumerated_caller
    (state : BountyStorageState) (account : String)
    (others : List String) (bountyId now deadline bond : Nat)
    (hnot : account ∉ others) :
    let oldClaims := (state.claimers account).getD []
    let next : BountyStorageState := { state with
      claimers := fun key => if key == account then
        some (oldClaims ++ [⟨bountyId, now, deadline, false, bond⟩])
        else state.claimers key }
    observedBountyCount next (account :: others) bountyId =
      observedBountyCount state (account :: others) bountyId + 1 := by
  have htail := observed_other_accounts_unchanged state account
    (some ((state.claimers account).getD [] ++
      [⟨bountyId, now, deadline, false, bond⟩])) others bountyId hnot
  simp only [observedBountyCount, List.map_cons, List.sum_cons] at ⊢
  simp [account_claim_count_append_matching]
  simp only [observedBountyCount] at htail
  simp at htail
  rw [htail]
  omega

theorem add_stored_claim_preserves_enumerated_coherence
    (state next : BountyStorageState) (account : String)
    (others : List String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hnot : account ∉ others)
    (hcoherent : coherentBountyCount state (account :: others) bountyId)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    coherentBountyCount next (account :: others) bountyId := by
  simp [addStoredClaim] at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · simp at hstep
      subst next
      have hobs := observed_count_adds_one_for_enumerated_caller
        state account others bountyId now deadline bond hnot
      simp only [coherentBountyCount] at hcoherent ⊢
      simpa [observedBountyCount, hcoherent] using hobs.symm

theorem add_stored_claim_preserves_other_bounty_coherence
    (state next : BountyStorageState) (account : String)
    (others : List String)
    (bountyId otherBounty now deadline maxDeadline times bond : Nat)
    (hnot : account ∉ others)
    (hother : otherBounty ≠ bountyId)
    (hcoherent : coherentBountyCount state
      (account :: others) otherBounty)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    coherentBountyCount next (account :: others) otherBounty := by
  simp [addStoredClaim] at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · simp at hstep
      subst next
      have hlocal := account_claim_count_append_other
        ((state.claimers account).getD []) bountyId otherBounty
        now deadline bond hother
      have hobs := observed_count_unchanged_when_local_same
        state account
        (some ((state.claimers account).getD [] ++
          [⟨bountyId, now, deadline, false, bond⟩]))
        others otherBounty hnot (by simpa using hlocal)
      simp only [coherentBountyCount] at hcoherent ⊢
      simpa [observedBountyCount, hother, hcoherent] using hobs.symm

theorem add_stored_claim_preserves_all_enumerated_coherence
    (state next : BountyStorageState) (account : String)
    (others : List String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hnot : account ∉ others)
    (hcoherent : coherentAllBountyCounts state (account :: others))
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    coherentAllBountyCounts next (account :: others) := by
  intro otherBounty
  by_cases hsame : otherBounty = bountyId
  · subst otherBounty
    exact add_stored_claim_preserves_enumerated_coherence state next
      account others bountyId now deadline maxDeadline times bond
      hnot (hcoherent bountyId) hstep
  · exact add_stored_claim_preserves_other_bounty_coherence state next
      account others bountyId otherBounty now deadline maxDeadline
      times bond hnot hsame (hcoherent otherBounty) hstep

theorem remove_first_bounty_claim_length
    (claims : List StoredBountyClaim) (bountyId : Nat)
    (found : StoredBountyClaim) (remaining : List StoredBountyClaim)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining)) :
    remaining.length + 1 = claims.length := by
  induction claims generalizing found remaining with
  | nil => simp [removeFirstBountyClaim] at hfind
  | cons claim rest ih =>
      by_cases hmatch : claim.bountyId = bountyId
      · simp [removeFirstBountyClaim, hmatch] at hfind
        rcases hfind with ⟨_, hremaining⟩
        subst remaining
        simp
      · cases hrec : removeFirstBountyClaim rest bountyId with
        | none => simp [removeFirstBountyClaim, hmatch, hrec] at hfind
        | some pair =>
            obtain ⟨inner, tail⟩ := pair
            simp [removeFirstBountyClaim, hmatch, hrec] at hfind
            rcases hfind with ⟨_, hremaining⟩
            subst remaining
            have hlen := ih inner tail hrec
            simp
            omega

theorem remove_first_bounty_claim_count
    (claims : List StoredBountyClaim) (bountyId : Nat)
    (found : StoredBountyClaim) (remaining : List StoredBountyClaim)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining)) :
    accountClaimCount remaining bountyId + 1 =
      accountClaimCount claims bountyId := by
  induction claims generalizing found remaining with
  | nil => simp [removeFirstBountyClaim] at hfind
  | cons claim rest ih =>
      by_cases hmatch : claim.bountyId = bountyId
      · simp [removeFirstBountyClaim, hmatch] at hfind
        rcases hfind with ⟨_, hremaining⟩
        subst remaining
        simp [accountClaimCount, hmatch]
      · cases hrec : removeFirstBountyClaim rest bountyId with
        | none => simp [removeFirstBountyClaim, hmatch, hrec] at hfind
        | some pair =>
            obtain ⟨inner, tail⟩ := pair
            simp [removeFirstBountyClaim, hmatch, hrec] at hfind
            rcases hfind with ⟨_, hremaining⟩
            subst remaining
            simpa [accountClaimCount, hmatch] using ih inner tail hrec

theorem observed_count_removes_one_for_enumerated_caller
    (state : BountyStorageState) (account : String)
    (others : List String) (bountyId : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hnot : account ∉ others)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining)) :
    let next : BountyStorageState := { state with
      claimers := fun key => if key == account then
        if remaining.isEmpty then none else some remaining
        else state.claimers key }
    observedBountyCount next (account :: others) bountyId + 1 =
      observedBountyCount state (account :: others) bountyId := by
  have htail := observed_other_accounts_unchanged state account
    (if remaining.isEmpty then none else some remaining)
    others bountyId hnot
  have hlocal := remove_first_bounty_claim_count claims bountyId
    found remaining hfind
  have hreplacement :
      (if remaining = [] then none else some remaining).getD [] =
        remaining := by
    cases remaining <;> rfl
  simp only [observedBountyCount, List.map_cons, List.sum_cons] at ⊢
  simp [hclaims]
  simp only [observedBountyCount] at htail
  simp at htail
  rw [htail]
  rw [hreplacement]
  omega

theorem remove_first_bounty_claim_preserves_other_bounty_entries
    (claims : List StoredBountyClaim) (bountyId otherBounty : Nat)
    (found : StoredBountyClaim) (remaining : List StoredBountyClaim)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hother : otherBounty ≠ bountyId) :
    remaining.filter (fun claim => claim.bountyId == otherBounty) =
      claims.filter (fun claim => claim.bountyId == otherBounty) := by
  induction claims generalizing found remaining with
  | nil => simp [removeFirstBountyClaim] at hfind
  | cons claim rest ih =>
      by_cases hmatch : claim.bountyId = bountyId
      · simp [removeFirstBountyClaim, hmatch] at hfind
        rcases hfind with ⟨_, hremaining⟩
        subst remaining
        have hnotOther : claim.bountyId ≠ otherBounty := by
          intro heq
          exact hother (heq.symm.trans hmatch)
        simp [hnotOther]
      · cases hrec : removeFirstBountyClaim rest bountyId with
        | none => simp [removeFirstBountyClaim, hmatch, hrec] at hfind
        | some pair =>
            obtain ⟨inner, tail⟩ := pair
            simp [removeFirstBountyClaim, hmatch, hrec] at hfind
            rcases hfind with ⟨_, hremaining⟩
            subst remaining
            by_cases hotherMatch : claim.bountyId = otherBounty
            · simp [List.filter, hotherMatch, ih inner tail hrec]
            · simp [List.filter, ih inner tail hrec]

theorem remove_stored_claim_exact
    (state : BountyStorageState) (account : String) (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count) :
    removeStoredClaim state account bountyId = some ({
      claimers := fun key => if key == account then
        if remaining.isEmpty then none else some remaining
        else state.claimers key
      counts := fun key => if key == bountyId then some (count - 1)
        else state.counts key
      locked := state.locked }, found) := by
  simp [removeStoredClaim, hclaims, hfind, hcount,
    Nat.ne_of_gt hpositive]

theorem remove_stored_claim_preserves_enumerated_coherence
    (state : BountyStorageState) (account : String)
    (others : List String) (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hnot : account ∉ others)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count)
    (hcoherent : coherentBountyCount state
      (account :: others) bountyId) :
    ∃ next, removeStoredClaim state account bountyId = some (next, found) ∧
      coherentBountyCount next (account :: others) bountyId := by
  let next : BountyStorageState := {
    claimers := fun key => if key == account then
      if remaining.isEmpty then none else some remaining
      else state.claimers key
    counts := fun key => if key == bountyId then some (count - 1)
      else state.counts key
    locked := state.locked }
  refine ⟨next, remove_stored_claim_exact state account bountyId count
    claims remaining found hclaims hfind hcount hpositive, ?_⟩
  have hobs := observed_count_removes_one_for_enumerated_caller
    state account others bountyId claims remaining found
    hnot hclaims hfind
  have hc : count = observedBountyCount state
      (account :: others) bountyId := by
    simpa [coherentBountyCount, hcount] using hcoherent
  have hobsNext : observedBountyCount next
      (account :: others) bountyId + 1 =
      observedBountyCount state (account :: others) bountyId := by
    simpa [next, observedBountyCount] using hobs
  have hcountNext : (next.counts bountyId).getD 0 = count - 1 := by
    simp [next]
  simp only [coherentBountyCount]
  rw [hcountNext]
  omega

theorem remove_stored_claim_preserves_other_bounty_coherence
    (state : BountyStorageState) (account : String)
    (others : List String) (bountyId otherBounty count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hnot : account ∉ others)
    (hother : otherBounty ≠ bountyId)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcoherent : coherentBountyCount state
      (account :: others) otherBounty) :
    let next : BountyStorageState := {
      claimers := fun key => if key == account then
        if remaining.isEmpty then none else some remaining
        else state.claimers key
      counts := fun key => if key == bountyId then some (count - 1)
        else state.counts key
      locked := state.locked }
    coherentBountyCount next (account :: others) otherBounty := by
  have hfilter := remove_first_bounty_claim_preserves_other_bounty_entries
    claims bountyId otherBounty found remaining hfind hother
  have hreplacement :
      (if remaining.isEmpty then none else some remaining).getD [] =
        remaining := by
    cases remaining <;> rfl
  have hlocal :
      accountClaimCount
        ((if remaining.isEmpty then none else some remaining).getD [])
        otherBounty =
      accountClaimCount ((state.claimers account).getD [])
        otherBounty := by
    rw [hreplacement, hclaims]
    exact congrArg List.length hfilter
  have hobs := observed_count_unchanged_when_local_same
    state account
    (if remaining.isEmpty then none else some remaining)
    others otherBounty hnot hlocal
  let next : BountyStorageState := {
    claimers := fun key => if key == account then
      if remaining.isEmpty then none else some remaining
      else state.claimers key
    counts := fun key => if key == bountyId then some (count - 1)
      else state.counts key
    locked := state.locked }
  have hcountNext : (next.counts otherBounty).getD 0 =
      (state.counts otherBounty).getD 0 := by
    simp [next, hother]
  have hobsNext : observedBountyCount next
      (account :: others) otherBounty =
      observedBountyCount state (account :: others) otherBounty := by
    simpa [next, observedBountyCount] using hobs
  simp only [coherentBountyCount]
  rw [hcountNext, hobsNext]
  exact hcoherent

theorem remove_stored_claim_preserves_all_enumerated_coherence
    (state : BountyStorageState) (account : String)
    (others : List String) (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hnot : account ∉ others)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count)
    (hcoherent : coherentAllBountyCounts state
      (account :: others)) :
    ∃ next, removeStoredClaim state account bountyId = some (next, found) ∧
      coherentAllBountyCounts next (account :: others) := by
  obtain ⟨next, hstep, htarget⟩ :=
    remove_stored_claim_preserves_enumerated_coherence state account
      others bountyId count claims remaining found hnot hclaims hfind
      hcount hpositive (hcoherent bountyId)
  refine ⟨next, hstep, ?_⟩
  intro otherBounty
  by_cases hsame : otherBounty = bountyId
  · subst otherBounty
    exact htarget
  · have hother := remove_stored_claim_preserves_other_bounty_coherence
      state account others bountyId otherBounty count claims remaining
      found hnot hsame hclaims hfind (hcoherent otherBounty)
    have hexact := remove_stored_claim_exact state account bountyId count
      claims remaining found hclaims hfind hcount hpositive
    rw [hexact] at hstep
    simp at hstep
    rcases hstep with ⟨hnext, _⟩
    simpa [coherentBountyCount, observedBountyCount] using hother

theorem remove_stored_claim_preserves_other_keys
    (state next : BountyStorageState) (account otherAccount : String)
    (bountyId otherBounty : Nat) (found : StoredBountyClaim)
    (hstep : removeStoredClaim state account bountyId = some (next, found))
    (hotherAccount : otherAccount ≠ account)
    (hotherBounty : otherBounty ≠ bountyId) :
    next.claimers otherAccount = state.claimers otherAccount ∧
      next.counts otherBounty = state.counts otherBounty ∧
      next.locked = state.locked := by
  cases hclaims : state.claimers account with
  | none => simp [removeStoredClaim, hclaims] at hstep
  | some claims =>
      cases hfind : removeFirstBountyClaim claims bountyId with
      | none => simp [removeStoredClaim, hclaims, hfind] at hstep
      | some pair =>
          obtain ⟨removed, remaining⟩ := pair
          cases hcount : state.counts bountyId with
          | none => simp [removeStoredClaim, hclaims, hfind, hcount] at hstep
          | some count =>
              by_cases hzero : count = 0
              · simp [removeStoredClaim, hclaims, hfind, hcount,
                  hzero] at hstep
              · simp [removeStoredClaim, hclaims, hfind, hcount,
                  hzero] at hstep
                rcases hstep with ⟨hnext, _⟩
                subst next
                simp [hotherAccount, hotherBounty]

theorem add_stored_claim_preserves_other_keys
    (state next : BountyStorageState) (account otherAccount : String)
    (bountyId otherBounty now deadline maxDeadline times bond : Nat)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next)
    (hotherAccount : otherAccount ≠ account)
    (hotherBounty : otherBounty ≠ bountyId) :
    next.claimers otherAccount = state.claimers otherAccount ∧
      next.counts otherBounty = state.counts otherBounty := by
  simp [addStoredClaim] at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · simp at hstep
      subst next
      simp [hotherAccount, hotherBounty]

theorem remove_first_of_two_bounties_keeps_other_entries :
    let first : StoredBountyClaim := ⟨7, 0, 10, true, 5⟩
    let other : StoredBountyClaim := ⟨8, 1, 10, false, 5⟩
    let later : StoredBountyClaim := ⟨7, 2, 10, false, 5⟩
    removeFirstBountyClaim [first, other, later] 7 =
      some (first, [other, later]) := by
  decide

end SputnikDAO2
