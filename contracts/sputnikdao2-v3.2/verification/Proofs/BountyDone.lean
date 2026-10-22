import Model.BountyDone
import Proofs.ProposalAct

namespace SputnikDAO2

theorem complete_first_claim_preserves_length
    (claims : List BondClaim) (account : String) :
    (completeFirstClaim claims account).length = claims.length := by
  induction claims with
  | nil => rfl
  | cons claim rest ih =>
      by_cases hmatch : claim.account = account
      · simp [completeFirstClaim, hmatch]
      · simp [completeFirstClaim, hmatch, ih]

theorem complete_first_claim_updates_first_match
    (claims : List BondClaim) (account : String)
    (found : BondClaim) (remaining : List BondClaim)
    (hfind : removeFirstClaim claims account = some (found, remaining)) :
    removeFirstClaim (completeFirstClaim claims account) account =
      some ({ found with completed := true }, remaining) := by
  induction claims generalizing found remaining with
  | nil => simp [removeFirstClaim] at hfind
  | cons claim rest ih =>
      by_cases hmatch : claim.account = account
      · simp [removeFirstClaim, completeFirstClaim, hmatch] at hfind ⊢
        rcases hfind with ⟨hfound, hremaining⟩
        subst found
        subst remaining
        simp [hmatch]
      · cases hrec : removeFirstClaim rest account with
        | none => simp [removeFirstClaim, hmatch, hrec] at hfind
        | some pair =>
            obtain ⟨inner, tail⟩ := pair
            simp [removeFirstClaim, hmatch, hrec] at hfind
            rcases hfind with ⟨hfound, hremaining⟩
            subst found
            subst remaining
            simp [completeFirstClaim, removeFirstClaim, hmatch,
              ih inner tail hrec]

theorem completed_first_claim_blocks_done
    (state : BountyDoneState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claim : BondClaim) (remaining : List BondClaim)
    (htarget : target.getD ctx.predecessor = account)
    (hfind : removeFirstClaim state.claims account =
      some (claim, remaining))
    (hcompleted : claim.completed = true) :
    bountyDone state ctx target bountyId description = none := by
  simp [bountyDone, htarget, hfind, hcompleted]

theorem expired_done_clears_claim_without_proposal_or_refund
    (state : BountyDoneState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claim : BondClaim) (remaining : List BondClaim)
    (htarget : target.getD ctx.predecessor = account)
    (hfind : removeFirstClaim state.claims account =
      some (claim, remaining))
    (hnotcompleted : claim.completed = false)
    (hvalid : validBountyDoneTime claim ctx.blockTimestamp = true)
    (hexpired : claim.start + claim.deadline < ctx.blockTimestamp)
    (hcount : 0 < state.claimCount) :
    bountyDone state ctx target bountyId description = some {
      state := { state with
        claims := remaining
        claimCount := state.claimCount - 1 }
      effect := .expiredClaimRemoved } := by
  simp [bountyDone, htarget, hfind, hnotcompleted, hvalid,
    hexpired, Nat.ne_of_gt hcount]

theorem active_done_requires_self_caller
    (state : BountyDoneState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claim : BondClaim) (remaining : List BondClaim)
    (htarget : target.getD ctx.predecessor = account)
    (hfind : removeFirstClaim state.claims account =
      some (claim, remaining))
    (hnotcompleted : claim.completed = false)
    (hvalid : validBountyDoneTime claim ctx.blockTimestamp = true)
    (hactive : ctx.blockTimestamp ≤ claim.start + claim.deadline)
    (hother : account ≠ ctx.predecessor) :
    bountyDone state ctx target bountyId description = none := by
  simp [bountyDone, htarget, hfind, hnotcompleted, hvalid,
    Nat.not_lt.mpr hactive, hother]

theorem active_done_marks_first_claim_after_proposal_creation
    (state : BountyDoneState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claim : BondClaim) (remaining : List BondClaim)
    (created : ProposalCreateState) (id : Nat)
    (htarget : target.getD ctx.predecessor = account)
    (hfind : removeFirstClaim state.claims account =
      some (claim, remaining))
    (hnotcompleted : claim.completed = false)
    (hvalid : validBountyDoneTime claim ctx.blockTimestamp = true)
    (hactive : ctx.blockTimestamp ≤ claim.start + claim.deadline)
    (hself : account = ctx.predecessor)
    (hcreate : addProposal state.proposals ctx
      (.bountyDone bountyId account) description = some (created, id)) :
    bountyDone state ctx target bountyId description = some {
      state := { state with
        claims := completeFirstClaim state.claims account
        proposals := created }
      effect := .proposalCreated id } := by
  subst account
  rw [hself] at hfind hcreate
  simp [bountyDone, hfind, hnotcompleted, hvalid,
    Nat.not_lt.mpr hactive, hcreate, hself]

theorem expired_third_party_clears_slot_even_without_proposal_bond :
    let state : BountyDoneState :=
      ⟨[⟨"alice.near", 0, 10, false, 5⟩], 1,
        ⟨0, 9, false, [], []⟩⟩
    let ctx : ProposalCreateContext :=
      ⟨"bob.near", 11, 1, 0, 4, false⟩
    (bountyDone state ctx (some "alice.near") 7 "done").map
      (fun result => decide (
        result.effect = .expiredClaimRemoved ∧
        result.state.claims = [] ∧
        result.state.claimCount = 0 ∧
        result.state.proposals = state.proposals)) = some true := by
  decide

theorem deadline_equality_submits_proposal_and_marks_completed :
    let state : BountyDoneState :=
      ⟨[⟨"alice.near", 0, 10, false, 5⟩], 1,
        ⟨0, 9, false, [], []⟩⟩
    let ctx : ProposalCreateContext :=
      ⟨"alice.near", 10, 1, 4, 4, true⟩
    (bountyDone state ctx none 7 "done").map
      (fun result => decide (
        result.effect = .proposalCreated 0 ∧
        result.state.claims = [⟨"alice.near", 0, 10, true, 5⟩] ∧
        result.state.claimCount = 1 ∧
        result.state.proposals.locked = 13)) = some true := by
  decide

theorem completed_first_duplicate_blocks_later_uncompleted_claim :
    let state : BountyDoneState :=
      ⟨[⟨"alice.near", 0, 10, true, 5⟩,
          ⟨"alice.near", 0, 10, false, 5⟩], 2,
        ⟨0, 10, false, [], []⟩⟩
    let ctx : ProposalCreateContext :=
      ⟨"alice.near", 20, 1, 4, 4, true⟩
    bountyDone state ctx none 7 "done" = none := by
  decide

theorem completed_first_matching_claim_blocks_done
    (state : BountyDoneState) (ctx : ProposalCreateContext)
    (target : String) (id : Nat) (description : String)
    (claim : BondClaim) (rest : List BondClaim)
    (hclaims : state.claims = claim :: rest)
    (haccount : claim.account = target)
    (hcompleted : claim.completed = true) :
    bountyDone state ctx (some target) id description = none := by
  simp [bountyDone, hclaims, removeFirstClaim, haccount, hcompleted]

theorem giveup_pending_done_preserves_proposal_records
    (state next : BountyDoneState) (account : String)
    (now forgiveness currentBond : Nat) (refund : Option Nat)
    (hstep : giveupPendingDone state account now forgiveness currentBond =
      some (next, refund)) :
    next.proposals.proposals = state.proposals.proposals ∧
      next.proposals.lastId = state.proposals.lastId := by
  cases hgiveup : bountyGiveup
      ⟨state.claims, state.claimCount, state.proposals.locked⟩
      account now forgiveness currentBond with
  | none => simp [giveupPendingDone, hgiveup] at hstep
  | some result =>
      obtain ⟨nextBonds, paid⟩ := result
      simp [giveupPendingDone, hgiveup] at hstep
      rcases hstep with ⟨hnext, _⟩
      subst next
      simp

theorem completed_claim_can_give_up_and_leave_pending_proposal :
    let initial : BountyDoneState :=
      ⟨[⟨"alice.near", 0, 10, false, 5⟩], 1,
        ⟨0, 5, false, [], []⟩⟩
    let ctx : ProposalCreateContext :=
      ⟨"alice.near", 1, 1, 4, 4, true⟩
    (bountyDone initial ctx none 7 "done").bind (fun done =>
      (giveupPendingDone done.state "alice.near" 2 20 5).map
        (fun result => decide (
          done.effect = .proposalCreated 0 ∧
          result.2 = some 5 ∧
          result.1.claims = [] ∧
          result.1.claimCount = 0 ∧
          result.1.proposals.locked = 4 ∧
          (proposalAt result.1.proposals.proposals 0).isSome = true ∧
          pendingDonePayout result.1 (some 1) .approved "alice.near" =
            none))) = some true := by
  decide

theorem old_pending_proposal_can_consume_fresh_uncompleted_claim :
    let initial : BountyDoneState :=
      ⟨[⟨"alice.near", 0, 10, false, 5⟩], 1,
        ⟨0, 5, false, [], []⟩⟩
    let ctx : ProposalCreateContext :=
      ⟨"alice.near", 1, 1, 4, 4, true⟩
    (bountyDone initial ctx none 7 "done").bind (fun done =>
      (giveupPendingDone done.state "alice.near" 2 20 5).bind
        (fun released =>
          (bountyClaim
            ⟨released.1.claims, released.1.claimCount,
              released.1.proposals.locked⟩
            "alice.near" 3 10 10 1 5 5).map
            (fun fresh => decide (
              fresh.claims = [⟨"alice.near", 3, 10, false, 5⟩] ∧
              (proposalAt released.1.proposals.proposals 0).isSome = true ∧
              (scheduleBountyPayout
                ⟨fresh, some 1, .approved⟩ "alice.near").map
                  (fun paid => decide (
                    paid.bonds.claims = [] ∧
                    paid.bonds.claimCount = 0 ∧
                    paid.bonds.locked = 9)) = some true)))) =
      some true := by
  decide

theorem authorized_remove_pending_done_leaves_claim_and_lock
    (state : BountyDoneState) (ctx : NonVoteContext)
    (id : Nat) (stored : CreatedProposal)
    (hlookup : proposalAt state.proposals.proposals id = some stored)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true) :
    ∃ next,
      removePendingDoneProposal state ctx id = some next ∧
      proposalAt next.proposals.proposals id = none ∧
      next.claims = state.claims ∧
      next.claimCount = state.claimCount ∧
      next.proposals.locked = state.proposals.locked := by
  let next : BountyDoneState :=
    { state with proposals := { state.proposals with
        proposals := eraseProposal state.proposals.proposals id } }
  refine ⟨next, ?_, ?_, rfl, rfl, rfl⟩
  · simp [removePendingDoneProposal, actNonVote, hlookup,
      hpermission, hkind, next]
  · exact erased_proposal_is_absent state.proposals.proposals id

end SputnikDAO2
