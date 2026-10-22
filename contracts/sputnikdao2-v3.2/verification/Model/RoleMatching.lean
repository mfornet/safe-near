import Model.PolicyRoleResolution
import Model.RoleMutation

namespace SputnikDAO2

/-! Projection of `RoleKind::match_user`. Group members are represented by a
list; `Nodup` is the explicit condition for its length to match the source
HashSet's role size. AccountId parsing and HashSet/Borsh representation are
outside this layer. -/

inductive MatchRoleKind where
  | everyone
  | member (minimum : Nat)
  | group (accounts : List String)
  deriving Repr, DecidableEq

def roleMatchesUser (kind : MatchRoleKind) (account : String)
    (delegated : Nat) : Bool :=
  match kind with
  | .everyone => true
  | .member minimum => delegated ≥ minimum
  | .group accounts => accounts.contains account

def statusKindOfMatchKind : MatchRoleKind → StatusRoleKind
  | .everyone => .everyone
  | .member _ => .member
  | .group accounts => .group accounts.length

structure MatchablePolicyRoleEntry where
  name : String
  kind : MatchRoleKind
  permissions : List String
  status : StatusRole
  deriving Repr, DecidableEq

def materializePolicyRole (account : String) (delegated : Nat)
    (entry : MatchablePolicyRoleEntry) : PolicyRoleEntry :=
  { auth :=
      { name := entry.name
        matchesUser := roleMatchesUser entry.kind account delegated
        permissions := entry.permissions
        weightKind := entry.status.weightKind }
    status := { entry.status with kind := statusKindOfMatchKind entry.kind } }

def materializePolicyRoles (account : String) (delegated : Nat)
    (entries : List MatchablePolicyRoleEntry) : List PolicyRoleEntry :=
  entries.map (materializePolicyRole account delegated)

def groupMembershipCanonical (entries : List MatchablePolicyRoleEntry) : Prop :=
  ∀ entry ∈ entries,
    match entry.kind with
    | .group accounts => accounts.Nodup
    | _ => True

def matchKindOfRoleShape : RoleShape → MatchRoleKind
  | .everyone => .everyone
  | .member minimum => .member minimum
  | .group accounts => .group accounts

def matchableFromMutable (role : MutableRole)
    (resolvedStatus : StatusRole) : MatchablePolicyRoleEntry :=
  ⟨role.name, matchKindOfRoleShape role.shape,
    role.permissions, resolvedStatus⟩

def matchableMutableRoles (roles : List MutableRole)
    (resolveStatus : MutableRole → StatusRole) :
    List MatchablePolicyRoleEntry :=
  roles.map (fun role => matchableFromMutable role (resolveStatus role))

end SputnikDAO2
