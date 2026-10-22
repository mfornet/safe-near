import Model.Policy
import Model.ProposalBonds

namespace SputnikDAO2

/-! Approved `ProposalKind::AddBounty` execution. The source writes a
VersionedBounty at `last_bounty_id`, checked-increments that u64, and returns
the old policy's proposal bond immediately. It does not validate times,
parse the token, or change the bounty claim count. `none` models atomic
abort on increment overflow; host rollback is a separate obligation. -/

structure BountyImage where
  description : String
  token : String
  amount : Nat
  times : Nat
  maxDeadline : Nat
  deriving Repr, DecidableEq

-- These are input-decoding constraints, not checks performed by
-- `internal_add_bounty`: Rust's U128/u32/U64 fields already have these widths.
def validBountyImage (bounty : BountyImage) : Prop :=
  bounty.amount ≤ maxU128 ∧ bounty.times ≤ maxU32 ∧
    bounty.maxDeadline ≤ maxU64

def bountyAt : List (Nat × BountyImage) → Nat → Option BountyImage
  | [], _ => none
  | (id, bounty) :: rest, target =>
      if id == target then some bounty else bountyAt rest target

def setBounty : List (Nat × BountyImage) → Nat → BountyImage →
    List (Nat × BountyImage)
  | [], id, bounty => [(id, bounty)]
  | (oldId, old) :: rest, id, bounty =>
      if oldId == id then (id, bounty) :: rest
      else (oldId, old) :: setBounty rest id bounty

structure AddBountyState where
  lastId : Nat
  bounties : List (Nat × BountyImage)
  claimCounts : Nat → Option Nat
  locked : Nat

structure AddBountyOutcome where
  state : AddBountyState
  createdId : Nat
  refund : BondTransfer
  callbackScheduled : Bool

def executeAddBounty (state : AddBountyState) (bounty : BountyImage)
    (oldProposalBond : Nat) (proposer : String) :
    Option AddBountyOutcome := do
  if state.lastId ≥ maxU64 then none else
  some {
    state := {
      lastId := state.lastId + 1
      bounties := setBounty state.bounties state.lastId bounty
      claimCounts := state.claimCounts
      locked := state.locked - oldProposalBond }
    createdId := state.lastId
    refund := ⟨proposer, oldProposalBond⟩
    callbackScheduled := false }

end SputnikDAO2
