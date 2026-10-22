import Model.Status

namespace SputnikDAO2

-- The four string patterns checked by `Policy::can_execute_action`.
def permissionGranted (permissions : List String) (kind action : String) : Bool :=
  permissions.contains (kind ++ ":" ++ action) ||
  permissions.contains (kind ++ ":*") ||
  permissions.contains ("*:" ++ action) ||
  permissions.contains "*:*"

structure AuthRole where
  name : String
  matchesUser : Bool
  permissions : List String
  weightKind : StatusWeightKind
  deriving Repr, DecidableEq

-- `get_user_roles` traverses the role vector and inserts a matching role's
-- permissions into a HashMap keyed by name. Later matching entries overwrite
-- earlier ones; an unmatched later entry does not overwrite.
def lastMatchingPermissions : List AuthRole → String → Option (List String)
  | [], _ => none
  | role :: rest, name =>
      match lastMatchingPermissions rest name with
      | some permissions => some permissions
      | none =>
          if role.name == name && role.matchesUser then some role.permissions
          else none

-- `internal_get_role` instead selects the first role with that name, without
-- checking whether the account matches its kind.
def firstRoleWeightKind : List AuthRole → String → Option StatusWeightKind
  | [], _ => none
  | role :: rest, name =>
      if role.name == name then some role.weightKind
      else firstRoleWeightKind rest name

def firstRole : List AuthRole → String → Option AuthRole
  | [], _ => none
  | role :: rest, name =>
      if role.name == name then some role
      else firstRole rest name

def namedRoleAllows (roles : List AuthRole) (name kind action : String) : Bool :=
  match lastMatchingPermissions roles name with
  | none => false
  | some permissions => permissionGranted permissions kind action

-- HashMap iteration chooses an unspecified ordering of its unique keys.
-- This list is a canonical enumeration of exactly the keys retained by
-- `get_user_roles` and accepted by `can_execute_action`; the runtime's Vec
-- may be any permutation of it.
def canonicalAllowedRoleNames (roles : List AuthRole)
    (kind action : String) : List String :=
  ((roles.map AuthRole.name).eraseDups).filter
    (fun name => namedRoleAllows roles name kind action)

def allowedRoleOrder (roles : List AuthRole) (kind action : String)
    (selected : List String) : Prop :=
  selected.Perm (canonicalAllowedRoleNames roles kind action)

-- The source's `allowed` Boolean is the OR of the same per-entry predicate
-- used to construct the output Vec.
def authorizationOutcome (roles : List AuthRole) (kind action : String)
    (selected : List String) (allowed : Bool) : Prop :=
  allowedRoleOrder roles kind action selected ∧ allowed = !selected.isEmpty

end SputnikDAO2
