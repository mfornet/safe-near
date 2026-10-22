import Model.Bonds
import Model.Proposal
import Model.ProposalBonds
import Model.Finalize

namespace SputnikDAO2

-- Projection for one bounty and one BountyDone proposal. `times = none` means
-- the bounty was removed. `locked` includes other deposits and bonds.
structure BountyResolutionState where
  bonds : BountyBondState
  times : Option Nat
  status : ProposalStatus
  deriving Repr, DecidableEq

-- `internal_execute_bounty_payout` removes the first matching claim before
-- constructing the payout promise. `none` represents its aborting guards.
-- The caller stores Approved separately before the asynchronous callback.
def scheduleBountyPayout (state : BountyResolutionState)
    (receiver : String) : Option BountyResolutionState := Id.run do
  if state.times.isNone then return none
  let some (_, remaining) := removeFirstClaim state.bonds.claims receiver |
    return none
  if state.bonds.claimCount == 0 then return none
  return some { state with
    bonds := { state.bonds with
      claims := remaining
      claimCount := state.bonds.claimCount - 1 } }

-- An unsuccessful payout callback only updates the proposal status. The
-- removed claim, bounty times and locked counter persist from scheduling.
def failedPayoutCallback (state : BountyResolutionState) : BountyResolutionState :=
  { state with status := .failed }

-- The successful callback runs with the CURRENT bond policy. For times = 1,
-- the source stores times = 0; it removes the bounty only if times was 0.
def successfulPayoutCallback (state : BountyResolutionState)
    (policy : BondPolicyAmounts) (proposer : String) :
    Option (BountyResolutionState × BondReturn) := Id.run do
  let some times := state.times | return none
  let refunded := returnProposalBonds state.bonds.locked policy proposer true
  return some (
    { state with
      bonds := { state.bonds with locked := refunded.lockedAfter }
      times := if times == 0 then none else some (times - 1)
      status := .approved },
    refunded)

inductive BountyRejection where
  | rejected | removed | expired
  deriving Repr, DecidableEq

def BountyRejection.status : BountyRejection → ProposalStatus
  | .rejected => .rejected
  | .removed => .removed
  | .expired => .expired

structure BountyRejectionResult where
  state : BountyResolutionState
  detachedRefunds : List BondTransfer
  proposalStored : Bool
  deriving Repr, DecidableEq

-- Rejected vote and Expired Finalize refund both current-policy bonds;
-- Removed vote deletes the proposal without refund. Both paths remove the
-- claim. `none` is an atomic abort, including any provisional bond scheduling.
def rejectBountyDone (state : BountyResolutionState) (receiver : String)
    (policy : BondPolicyAmounts) (proposer : String)
    (kind : BountyRejection) : Option BountyRejectionResult := Id.run do
  let some claimRemoved := scheduleBountyPayout state receiver | return none
  let refund := returnProposalBonds claimRemoved.bonds.locked policy proposer true
  let returnBonds := kind != .removed
  return some {
    state := { claimRemoved with
      bonds := { claimRemoved.bonds with
        locked := if returnBonds then refund.lockedAfter
          else claimRemoved.bonds.locked }
      status := kind.status }
    detachedRefunds := if returnBonds then
      refund.detachedTransfers ++ [refund.returnedTransfer] else []
    proposalStored := returnBonds }

-- Connect the Expired branch of the ordered-role Finalize selector to bounty
-- claim removal and refund scheduling. Other selected effects do not enter.
def scheduleBountyExpiry (ctx : FinalizeContext)
    (state : BountyResolutionState) (receiver : String)
    (policy : BondPolicyAmounts) (proposer : String) :
    Option BountyRejectionResult := Id.run do
  let some plan := selectFinalize ctx | return none
  if plan.effect != .expireAndReturnBonds then return none
  return rejectBountyDone state receiver policy proposer .expired

end SputnikDAO2
