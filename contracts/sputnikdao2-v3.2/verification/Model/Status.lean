import Model.Proposal

namespace SputnikDAO2

inductive StatusRoleKind where
  | everyone | group (size : Nat) | member
  deriving Repr, DecidableEq

inductive StatusWeightKind where
  | role | token
  deriving Repr, DecidableEq

structure StatusRole where
  kind : StatusRoleKind
  weightKind : StatusWeightKind
  quorum : Nat
  threshold : WeightOrRatio
  approvals : Nat
  rejections : Nat
  removals : Nat
  deriving Repr, DecidableEq

def roleTotal (role : StatusRole) (totalSupply : Nat) : Nat :=
  match role.kind with
  | .everyone => 0
  | .group size => if role.weightKind == .role then size else totalSupply
  | .member => totalSupply

-- Everyone is skipped, rather than allowed to decide with zero total.
def roleDecision (role : StatusRole) (totalSupply : Nat) : Decision :=
  match role.kind with
  | .everyone => .inProgress
  | _ =>
      decideRole
        (voteThreshold role.quorum role.threshold (roleTotal role totalSupply))
        role.approvals role.rejections role.removals

-- Projection of `Policy::proposal_status` after successful role-name lookup,
-- serialization and arithmetic. The input list is in the actual caller-supplied
-- order. `none` is the source's status guard failure. `expired` uses Nat time;
-- the u64 addition boundary must be discharged when refining to Rust/Wasm.
def proposalStatusForRoles (original : ProposalStatus)
    (submission period now totalSupply : Nat) (roles : List StatusRole) :
    Option ProposalStatus := Id.run do
  if original != .inProgress && original != .failed then return none
  if expired submission period now then return some .expired
  let decision := firstDecisive (roles.map (roleDecision · totalSupply))
  return some <| if decision == .inProgress then original else decisionStatus decision

end SputnikDAO2
