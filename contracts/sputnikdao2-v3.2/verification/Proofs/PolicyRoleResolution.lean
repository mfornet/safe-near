import Model.PolicyRoleResolution
import Proofs.Authorization

namespace SputnikDAO2

theorem policy_name_has_first_status_role
    (entries : List PolicyRoleEntry) (name : String)
    (h : name ∈ (policyAuthProjection entries).map AuthRole.name) :
    ∃ role, firstStatusRole entries name = some role := by
  induction entries with
  | nil => simp [policyAuthProjection] at h
  | cons entry rest ih =>
      by_cases heq : entry.auth.name = name
      · exact ⟨entry.status, by simp [firstStatusRole, heq]⟩
      · have hrest : name ∈ (policyAuthProjection rest).map AuthRole.name := by
          simpa [policyAuthProjection, Ne.symm heq] using h
        obtain ⟨role, hr⟩ := ih hrest
        exact ⟨role, by simp [firstStatusRole, heq, hr]⟩

theorem authorized_name_has_first_status_role
    (entries : List PolicyRoleEntry) (kind action : String)
    (selected : List String)
    (horder : allowedRoleOrder (policyAuthProjection entries)
      kind action selected)
    (name : String) (hname : name ∈ selected) :
    ∃ role, firstStatusRole entries name = some role := by
  have hallowed := (authorized_order_membership
    (policyAuthProjection entries) kind action selected horder name).mp hname
  exact policy_name_has_first_status_role entries name
    (allowed_name_occurs_in_policy
      (policyAuthProjection entries) name kind action hallowed)

private theorem selected_names_resolve_when_present
    (entries : List PolicyRoleEntry) (selected : List String)
    (hall : ∀ name ∈ selected,
      ∃ role, firstStatusRole entries name = some role) :
    ∃ resolved, resolveSelectedStatusRoles entries selected = some resolved := by
  induction selected with
  | nil => exact ⟨[], rfl⟩
  | cons name rest ih =>
      obtain ⟨role, hrole⟩ := hall name (by simp)
      have hrest : ∀ other ∈ rest,
          ∃ rule, firstStatusRole entries other = some rule := by
        intro other hmem
        exact hall other (by simp [hmem])
      obtain ⟨tail, htail⟩ := ih hrest
      exact ⟨role :: tail,
        by simp [resolveSelectedStatusRoles, hrole, htail]⟩

theorem authorized_names_resolve_in_order
    (entries : List PolicyRoleEntry) (kind action : String)
    (selected : List String)
    (horder : allowedRoleOrder (policyAuthProjection entries)
      kind action selected) :
    ∃ resolved, resolveSelectedStatusRoles entries selected = some resolved := by
  apply selected_names_resolve_when_present entries selected
  intro name hname
  exact authorized_name_has_first_status_role entries kind action
    selected horder name hname

theorem resolved_roles_are_first_named_entries
    (entries : List PolicyRoleEntry) (selected : List String)
    (resolved : List StatusRole)
    (h : resolveSelectedStatusRoles entries selected = some resolved) :
    ResolvedFirstRoles entries selected resolved := by
  induction selected generalizing resolved with
  | nil =>
      simp [resolveSelectedStatusRoles] at h
      cases h
      exact ResolvedFirstRoles.nil
  | cons name rest ih =>
      simp only [resolveSelectedStatusRoles] at h
      cases hfirst : firstStatusRole entries name with
      | none => simp [hfirst] at h
      | some role =>
          simp [hfirst] at h
          cases htail : resolveSelectedStatusRoles entries rest with
          | none => simp [htail] at h
          | some tail =>
              simp [htail] at h
              cases h
              exact ResolvedFirstRoles.cons name role rest tail hfirst (ih tail htail)

theorem first_named_status_uses_first_weight_kind
    (entries : List PolicyRoleEntry) (name : String)
    (role : StatusRole)
    (hcoherent : roleEntriesWeightCoherent entries)
    (hfirst : firstStatusRole entries name = some role) :
    firstRoleWeightKind (policyAuthProjection entries) name =
      some role.weightKind := by
  induction entries with
  | nil => simp [firstStatusRole] at hfirst
  | cons entry rest ih =>
      by_cases heq : entry.auth.name = name
      · have hw := hcoherent entry (by simp)
        simp [firstStatusRole, heq] at hfirst
        cases hfirst
        simp [firstRoleWeightKind, policyAuthProjection, heq, hw]
      · have hrest : roleEntriesWeightCoherent rest := by
          intro other hmem
          exact hcoherent other (by simp [hmem])
        have ht : firstStatusRole rest name = some role := by
          simpa [firstStatusRole, heq] using hfirst
        simpa [firstRoleWeightKind, policyAuthProjection, heq]
          using ih hrest ht

theorem authorized_order_admits_resolved_ballot
    (entries : List PolicyRoleEntry) (kind action : String)
    (selected : List String)
    (horder : allowedRoleOrder (policyAuthProjection entries)
      kind action selected) :
    ∃ ballot : MultiVoteState,
      ballot.status = .inProgress ∧ ballot.voters = [] ∧
      authorizedResolvedBallot entries kind action selected ballot := by
  obtain ⟨resolved, hresolved⟩ :=
    authorized_names_resolve_in_order entries kind action selected horder
  exact ⟨⟨.inProgress, [], resolved⟩,
    rfl, rfl, horder, hresolved⟩

theorem authorized_ballot_uses_first_named_status_rules
    (entries : List PolicyRoleEntry) (kind action : String)
    (selected : List String) (ballot : MultiVoteState)
    (h : authorizedResolvedBallot entries kind action selected ballot) :
    ResolvedFirstRoles entries selected ballot.selectedRoles := by
  exact resolved_roles_are_first_named_entries entries selected
    ballot.selectedRoles h.2

theorem duplicate_name_permission_and_status_sources_differ :
    let firstStatus : StatusRole :=
      ⟨.group 1, .role, 0, .weight 1, 0, 0, 0⟩
    let secondStatus : StatusRole :=
      ⟨.member, .token, 0, .ratio 1 1, 0, 0, 0⟩
    let entries : List PolicyRoleEntry :=
      [⟨⟨"council", false, [], .role⟩, firstStatus⟩,
       ⟨⟨"council", true, ["*:VoteApprove"], .token⟩, secondStatus⟩]
    canonicalAllowedRoleNames (policyAuthProjection entries)
      "vote" "VoteApprove" = ["council"] ∧
    resolveSelectedStatusRoles entries ["council"] = some [firstStatus] := by
  decide

end SputnikDAO2
