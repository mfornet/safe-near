import Model.RoleMatching
import Proofs.PolicyRoleResolution
import Proofs.GroupSetInvariant

namespace SputnikDAO2

theorem everyone_matches_any_user (account : String) (delegated : Nat) :
    roleMatchesUser .everyone account delegated = true := by rfl

theorem member_matches_at_threshold (account : String)
    (minimum delegated : Nat) :
    roleMatchesUser (.member minimum) account delegated = true ↔
      minimum ≤ delegated := by
  simp [roleMatchesUser]

theorem group_matches_exact_membership (accounts : List String)
    (account : String) (delegated : Nat) :
    roleMatchesUser (.group accounts) account delegated = true ↔
      account ∈ accounts := by
  simp [roleMatchesUser]

theorem materialized_entry_uses_computed_match
    (entry : MatchablePolicyRoleEntry) (account : String)
    (delegated : Nat) :
    (materializePolicyRole account delegated entry).auth.matchesUser =
      roleMatchesUser entry.kind account delegated ∧
    (materializePolicyRole account delegated entry).status.kind =
      statusKindOfMatchKind entry.kind := by
  constructor <;> rfl

theorem materialized_roles_have_coherent_weight_kind
    (entries : List MatchablePolicyRoleEntry) (account : String)
    (delegated : Nat) :
    roleEntriesWeightCoherent
      (materializePolicyRoles account delegated entries) := by
  intro entry hentry
  simp [materializePolicyRoles] at hentry
  rcases hentry with ⟨source, _, heq⟩
  subst entry
  rfl

theorem materialized_authorized_order_resolves
    (entries : List MatchablePolicyRoleEntry)
    (account : String) (delegated : Nat)
    (kind action : String) (selected : List String)
    (horder : allowedRoleOrder
      (policyAuthProjection (materializePolicyRoles account delegated entries))
      kind action selected) :
    ∃ ballot : MultiVoteState,
      ballot.status = .inProgress ∧ ballot.voters = [] ∧
      authorizedResolvedBallot
        (materializePolicyRoles account delegated entries)
        kind action selected ballot := by
  exact authorized_order_admits_resolved_ballot
    (materializePolicyRoles account delegated entries)
    kind action selected horder

theorem zero_weight_matches_zero_threshold_member :
    roleMatchesUser (.member 0) "alice.near" 0 = true ∧
    roleMatchesUser (.member 1) "alice.near" 0 = false := by
  decide

theorem canonical_mutable_roles_materialize_canonical_groups
    (roles : List MutableRole)
    (resolveStatus : MutableRole → StatusRole)
    (h : canonicalMutableRoles roles) :
    groupMembershipCanonical
      (matchableMutableRoles roles resolveStatus) := by
  intro entry hentry
  simp [matchableMutableRoles] at hentry
  rcases hentry with ⟨source, hsource, heq⟩
  subst entry
  have hcanonical := h source hsource
  cases hshape : source.shape <;>
    simp [matchableFromMutable, matchKindOfRoleShape,
      canonicalMutableRole, hshape] at hcanonical ⊢
  all_goals assumption

end SputnikDAO2
