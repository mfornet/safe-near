import Model.PolicyArithmetic

namespace SputnikDAO2

/-! Selected-role projection of the vote branch in `act_proposal`. The role
list is the actual order returned by `can_execute_action`; it may vary with
HashMap iteration. Each `StatusRole` carries the existing stored counts for
that name and the first matching policy role's voting rules. Counts for
unselected roles, receipt effects and storage writes remain outside this
projection. -/

structure MultiVoteState where
  status : ProposalStatus
  voters : List String
  selectedRoles : List StatusRole
  deriving Repr, DecidableEq

def roleVoteAmount (role : StatusRole) (userWeight : Nat) : Nat :=
  if role.weightKind == .token then userWeight else 1

def countSelectedRole (role : StatusRole) (choice : VoteChoice)
    (userWeight : Nat) : Option StatusRole :=
  let amount := roleVoteAmount role userWeight
  match choice with
  | .approve =>
      if role.approvals + amount > maxU128 then none
      else some { role with approvals := role.approvals + amount }
  | .reject =>
      if role.rejections + amount > maxU128 then none
      else some { role with rejections := role.rejections + amount }
  | .remove =>
      if role.removals + amount > maxU128 then none
      else some { role with removals := role.removals + amount }

def countSelectedRoles (roles : List StatusRole) (choice : VoteChoice)
    (userWeight : Nat) : Option (List StatusRole) := do
  match roles with
  | [] => some []
  | role :: rest =>
      let counted ← countSelectedRole role choice userWeight
      let tail ← countSelectedRoles rest choice userWeight
      some (counted :: tail)

-- The source increments every selected role before inserting the voter, then
-- calls `proposal_status`, which checks strict expiration before roles.
-- `none` represents an atomic abort, including checked u128 count addition
-- and checked u64 submission-time addition. The checked status projection
-- also aborts on ratio overflow; policy lookup and serialization remain
-- refinement inputs.
def multiVoteStep (state : MultiVoteState) (account : String)
    (choice : VoteChoice) (userWeight submission period now totalSupply : Nat) :
    Option MultiVoteState := do
  if state.status != .inProgress then none else
  if state.voters.contains account then none else
  if userWeight > maxU128 || totalSupply > maxU128 ||
      submission > maxU64 || period > maxU64 || now > maxU64 ||
      submission + period > maxU64 then none else
  let counted ← countSelectedRoles state.selectedRoles choice userWeight
  let status ← proposalStatusChecked .inProgress submission period now
      totalSupply counted
  some { status := status
         voters := account :: state.voters
         selectedRoles := counted }

end SputnikDAO2
