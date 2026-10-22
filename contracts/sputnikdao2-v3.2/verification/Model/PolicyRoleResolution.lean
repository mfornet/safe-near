import Model.Authorization
import Model.MultiVote

namespace SputnikDAO2

/-! One policy-vector entry supplies both authorization metadata and the
resolved status rule. `can_execute_action` uses the last matching permission
entry per name, while `internal_get_role` takes the first entry with that
name, even if that first entry did not match the caller. User matching is
supplied here and derived from role kinds in `Model.RoleMatching`; concrete
role/count decoding remains an input. -/

structure PolicyRoleEntry where
  auth : AuthRole
  status : StatusRole
  deriving Repr, DecidableEq

def policyAuthProjection (entries : List PolicyRoleEntry) : List AuthRole :=
  entries.map PolicyRoleEntry.auth

def roleEntriesWeightCoherent (entries : List PolicyRoleEntry) : Prop :=
  ∀ entry ∈ entries, entry.auth.weightKind = entry.status.weightKind

def firstStatusRole : List PolicyRoleEntry → String → Option StatusRole
  | [], _ => none
  | entry :: rest, name =>
      if entry.auth.name == name then some entry.status
      else firstStatusRole rest name

def resolveSelectedStatusRoles (entries : List PolicyRoleEntry) :
    List String → Option (List StatusRole)
  | [] => some []
  | name :: rest => do
      let role ← firstStatusRole entries name
      let tail ← resolveSelectedStatusRoles entries rest
      some (role :: tail)

inductive ResolvedFirstRoles (entries : List PolicyRoleEntry) :
    List String → List StatusRole → Prop where
  | nil : ResolvedFirstRoles entries [] []
  | cons (name : String) (role : StatusRole)
      (names : List String) (roles : List StatusRole)
      (hfirst : firstStatusRole entries name = some role)
      (htail : ResolvedFirstRoles entries names roles) :
      ResolvedFirstRoles entries (name :: names) (role :: roles)

def authorizedResolvedBallot (entries : List PolicyRoleEntry)
    (kind action : String) (selected : List String)
    (ballot : MultiVoteState) : Prop :=
  allowedRoleOrder (policyAuthProjection entries) kind action selected ∧
  resolveSelectedStatusRoles entries selected = some ballot.selectedRoles

end SputnikDAO2
