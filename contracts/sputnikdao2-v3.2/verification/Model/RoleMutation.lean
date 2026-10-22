import Model.ProposalBonds

namespace SputnikDAO2

/-! Projection of the five policy role/vote-policy mutation helpers used by
approved synchronous proposals. Names are deliberately not assumed unique.
Group members represent a set; permissions and vote-policy contents are
opaque values copied with the role. -/

inductive RoleShape where
  | everyone
  | member (threshold : Nat)
  | group (members : List String)
  deriving Repr, DecidableEq

structure MutableRole where
  name : String
  shape : RoleShape
  permissions : List String
  votePolicyTag : String
  deriving Repr, DecidableEq

def canonicalMutableRole (role : MutableRole) : Prop :=
  match role.shape with
  | .group members => members.Nodup
  | _ => True

def canonicalMutableRoles (roles : List MutableRole) : Prop :=
  ∀ role ∈ roles, canonicalMutableRole role

inductive RoleEffect where
  | none
  | added
  | updated
  | missing
  | wrongKind
  deriving Repr, DecidableEq

def insertGroupMember (members : List String) (member : String) : List String :=
  if members.contains member then members else members ++ [member]

def deleteGroupMember (members : List String) (member : String) : List String :=
  members.filter (· != member)

def replaceOrAppendRole : List MutableRole → MutableRole →
    List MutableRole × RoleEffect
  | [], role => ([role], .added)
  | old :: rest, role =>
      if old.name == role.name then (role :: rest, .updated)
      else
        let (next, effect) := replaceOrAppendRole rest role
        (old :: next, effect)

def removeFirstRole : List MutableRole → String →
    List MutableRole × RoleEffect
  | [], _ => ([], .missing)
  | old :: rest, name =>
      if old.name == name then (rest, .none)
      else
        let (next, effect) := removeFirstRole rest name
        (old :: next, effect)

def changeFirstMember : List MutableRole → String → String → Bool →
    List MutableRole × RoleEffect
  | [], _, _, _ => ([], .missing)
  | old :: rest, name, member, add =>
      if old.name == name then
        match old.shape with
        | .group members =>
            let next := if add then insertGroupMember members member
              else deleteGroupMember members member
            ({ old with shape := .group next } :: rest, .none)
        | _ => (old :: rest, .wrongKind)
      else
        let (next, effect) := changeFirstMember rest name member add
        (old :: next, effect)

structure MutablePolicyImage where
  roles : List MutableRole
  defaultVotePolicyTag : String
  proposalBond : Nat
  deriving Repr, DecidableEq

inductive RoleMutationAction where
  | addOrUpdate (role : MutableRole)
  | remove (name : String)
  | addMember (name member : String)
  | removeMember (name member : String)
  | updateDefaultVotePolicy (tag : String)
  deriving Repr, DecidableEq

def canonicalRoleMutationAction : RoleMutationAction → Prop
  | .addOrUpdate role => canonicalMutableRole role
  | _ => True

def mutatePolicy (policy : MutablePolicyImage) (action : RoleMutationAction) :
    MutablePolicyImage × RoleEffect :=
  match action with
  | .addOrUpdate role =>
      let (roles, effect) := replaceOrAppendRole policy.roles role
      ({ policy with roles := roles }, effect)
  | .remove name =>
      let (roles, effect) := removeFirstRole policy.roles name
      ({ policy with roles := roles }, effect)
  | .addMember name member =>
      let (roles, effect) := changeFirstMember policy.roles name member true
      ({ policy with roles := roles }, effect)
  | .removeMember name member =>
      let (roles, effect) := changeFirstMember policy.roles name member false
      ({ policy with roles := roles }, effect)
  | .updateDefaultVotePolicy tag =>
      ({ policy with defaultVotePolicyTag := tag }, .none)

structure RoleMutationOutcome where
  policy : MutablePolicyImage
  locked : Nat
  refund : BondTransfer
  effect : RoleEffect
  callbackScheduled : Bool
  deriving Repr, DecidableEq

def executeRoleMutation (policy : MutablePolicyImage) (locked : Nat)
    (action : RoleMutationAction) (proposer : String) : RoleMutationOutcome :=
  let (next, effect) := mutatePolicy policy action
  ⟨next, locked - policy.proposalBond,
    ⟨proposer, policy.proposalBond⟩, effect, false⟩

end SputnikDAO2
