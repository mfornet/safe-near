import Model.PolicyArithmetic
import Model.ProposalBonds

namespace SputnikDAO2

inductive FinalizeEffect where
  | executeProposal | expireAndReturnBonds
  deriving Repr, DecidableEq

structure FinalizePlan where
  storedStatus : ProposalStatus
  effect : FinalizeEffect
  deriving Repr, DecidableEq

structure FinalizeContext where
  proposalExists : Bool
  permissionAllowed : Bool
  exactKindMatches : Bool
  originalStatus : ProposalStatus
  submission : Nat
  period : Nat
  now : Nat
  totalSupply : Nat
  policyRolesInVectorOrder : List StatusRole
  deriving Repr, DecidableEq

-- Branch selection for `Action::Finalize` after the global/local action log
-- update. The role list is policy vector order, unlike a vote's HashMap order.
-- `some` selects a branch; its execution, bond receipts, callbacks and final
-- state commit can still fail and are outside this projection.
def selectFinalize (ctx : FinalizeContext) : Option FinalizePlan := Id.run do
  if !ctx.proposalExists then return none
  if !ctx.permissionAllowed then return none
  if !ctx.exactKindMatches then return none
  let some status := proposalStatusChecked ctx.originalStatus
    ctx.submission ctx.period ctx.now ctx.totalSupply
    ctx.policyRolesInVectorOrder | return none
  match status with
  | .approved => return some ⟨.approved, .executeProposal⟩
  | .expired => return some ⟨.expired, .expireAndReturnBonds⟩
  | _ => return none

structure OrdinaryExpiryPlan where
  storedStatus : ProposalStatus
  lockedAfter : Nat
  detachedRefund : BondTransfer
  proposalStored : Bool
  deriving Repr, DecidableEq

-- The ordinary (non-BountyDone) Expired path of `act_proposal`: the helper's
-- returned bond promise is detached by `internal_reject_proposal`, then the
-- updated proposal is stored. This is receipt scheduling, not transfer success.
def scheduleOrdinaryExpiry (ctx : FinalizeContext) (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String) :
    Option OrdinaryExpiryPlan := Id.run do
  let some plan := selectFinalize ctx | return none
  if plan.effect != .expireAndReturnBonds then return none
  let bonds := returnProposalBonds locked policy proposer false
  return some ⟨plan.storedStatus, bonds.lockedAfter,
    bonds.returnedTransfer, true⟩

end SputnikDAO2
