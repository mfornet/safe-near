import Model.Bonds
import Model.ProposalCreate
import Model.BountyResolution
import Model.ProposalAct

namespace SputnikDAO2

-- One bounty id, with the proposal store sharing the source's locked counter.
-- Other bounty IDs in each account's vector are outside this projection.
structure BountyDoneState where
  claims : List BondClaim
  claimCount : Nat
  proposals : ProposalCreateState
  deriving Repr, DecidableEq

inductive BountyDoneEffect where
  | expiredClaimRemoved
  | proposalCreated (id : Nat)
  deriving Repr, DecidableEq

structure BountyDoneResult where
  state : BountyDoneState
  effect : BountyDoneEffect
  deriving Repr, DecidableEq

-- Preserve vector order while setting the first matching claim's completed
-- bit, as the source does after a successful `add_proposal` call.
def completeFirstClaim : List BondClaim → String → List BondClaim
  | [], _ => []
  | claim :: rest, account =>
      if claim.account == account then
        { claim with completed := true } :: rest
      else claim :: completeFirstClaim rest account

def validBountyDoneTime (claim : BondClaim) (now : Nat) : Bool :=
  claim.start ≤ maxU64 && claim.deadline ≤ maxU64 &&
    now ≤ maxU64 && claim.start + claim.deadline ≤ maxU64

-- Projection of `bounty_done` after SDK argument decoding. `target = none`
-- selects the predecessor. Expired cleanup needs no self-caller or bond
-- check; active completion delegates the exact bond, permission, ID and lock
-- checks to `addProposal`. A completed *first* claim aborts before expiry.
-- `none` is an atomic abort, including provisional proposal writes.
def bountyDone (state : BountyDoneState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description : String) :
    Option BountyDoneResult := Id.run do
  let account := target.getD ctx.predecessor
  let some (claim, remaining) := removeFirstClaim state.claims account |
    return none
  if claim.completed then return none
  if !validBountyDoneTime claim ctx.blockTimestamp then return none
  if ctx.blockTimestamp > claim.start + claim.deadline then
    if state.claimCount == 0 then return none
    return some {
      state := { state with
        claims := remaining
        claimCount := state.claimCount - 1 }
      effect := .expiredClaimRemoved }
  if account != ctx.predecessor then return none
  let some (created, id) := addProposal state.proposals ctx
    (.bountyDone bountyId account) description | return none
  return some {
    state := { state with
      claims := completeFirstClaim state.claims account
      proposals := created }
    effect := .proposalCreated id }

-- `bounty_giveup` has no completed-claim guard. Its claim and lock mutation
-- leaves any already-created BountyDone proposal in the proposal map.
def giveupPendingDone (state : BountyDoneState) (account : String)
    (now forgiveness currentBond : Nat) :
    Option (BountyDoneState × Option Nat) := Id.run do
  let bonds : BountyBondState :=
    ⟨state.claims, state.claimCount, state.proposals.locked⟩
  let some (nextBonds, refund) :=
    bountyGiveup bonds account now forgiveness currentBond | return none
  return some (
    { state with
      claims := nextBonds.claims
      claimCount := nextBonds.claimCount
      proposals := { state.proposals with locked := nextBonds.locked } },
    refund)

def pendingDonePayout (state : BountyDoneState) (times : Option Nat)
    (status : ProposalStatus) (receiver : String) :
    Option BountyResolutionState :=
  scheduleBountyPayout
    ⟨⟨state.claims, state.claimCount, state.proposals.locked⟩,
      times, status⟩ receiver

-- `Action::RemoveProposal` is a separate path from `VoteRemove`. It deletes
-- the proposal without invoking the bounty rejection helper, so the claim
-- vector, count and lock are unchanged. The global action log is projected
-- away here; `actNonVote` models its update separately.
def removePendingDoneProposal (state : BountyDoneState)
    (ctx : NonVoteContext) (proposalId : Nat) : Option BountyDoneState := do
  let before : NonVoteState :=
    ⟨state.proposals.proposals, [], state.proposals.locked⟩
  let after ← actNonVote before ctx proposalId .removeProposal
  some { state with proposals := { state.proposals with
    proposals := after.proposals, locked := after.locked } }

end SputnikDAO2
