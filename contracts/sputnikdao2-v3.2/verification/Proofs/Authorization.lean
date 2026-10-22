import Model.Authorization
import Proofs.Policy

namespace SputnikDAO2

theorem no_name_no_matching_permissions (roles : List AuthRole) (name : String)
    (h : name ∉ roles.map AuthRole.name) :
    lastMatchingPermissions roles name = none := by
  induction roles with
  | nil => rfl
  | cons role rest ih =>
      have hrole : role.name ≠ name := by
        intro heq
        apply h
        simp [heq]
      have hrest : name ∉ rest.map AuthRole.name := by
        intro hmem
        apply h
        simp [hmem]
      simp [lastMatchingPermissions, ih hrest, hrole]

theorem unique_names_align_permission_lookup (roles : List AuthRole)
    (name : String) (h : (roles.map AuthRole.name).Nodup) :
    lastMatchingPermissions roles name =
      (firstRole roles name).bind fun role =>
        if role.matchesUser then some role.permissions else none := by
  induction roles with
  | nil => rfl
  | cons role rest ih =>
      have hnot : role.name ∉ rest.map AuthRole.name :=
        (List.nodup_cons.mp h).1
      have htail : (rest.map AuthRole.name).Nodup :=
        (List.nodup_cons.mp h).2
      by_cases heq : role.name = name
      · subst name
        have hnone := no_name_no_matching_permissions rest role.name hnot
        simp [lastMatchingPermissions, firstRole, hnone]
      · cases hf : firstRole rest name with
        | none => simp [lastMatchingPermissions, firstRole, heq, ih htail, hf]
        | some found =>
            cases hm : found.matchesUser <;>
              simp [lastMatchingPermissions, firstRole, heq, ih htail, hf, hm]

theorem exact_permission_grants :
    permissionGranted ["transfer:VoteApprove"] "transfer" "VoteApprove" = true := by
  decide

theorem kind_wildcard_grants :
    permissionGranted ["transfer:*"] "transfer" "VoteReject" = true := by
  decide

theorem action_wildcard_grants :
    permissionGranted ["*:VoteApprove"] "vote" "VoteApprove" = true := by
  decide

theorem global_wildcard_grants :
    permissionGranted ["*:*"] "upgrade_self" "Finalize" = true := by
  decide

theorem unrelated_permission_denies :
    permissionGranted ["vote:VoteApprove"] "transfer" "VoteApprove" = false := by
  decide

theorem later_matching_name_overwrites_permissions :
    let roles : List AuthRole :=
      [⟨"council", true, [], .role⟩,
       ⟨"council", true, ["*:VoteApprove"], .token⟩]
    lastMatchingPermissions roles "council" = some ["*:VoteApprove"] ∧
    firstRoleWeightKind roles "council" = some .role ∧
    namedRoleAllows roles "council" "transfer" "VoteApprove" = true := by
  decide

theorem unmatched_later_name_does_not_overwrite :
    let roles : List AuthRole :=
      [⟨"council", true, ["transfer:VoteApprove"], .role⟩,
       ⟨"council", false, [], .token⟩]
    lastMatchingPermissions roles "council" =
      some ["transfer:VoteApprove"] := by
  decide

theorem permission_can_come_from_later_role_while_weight_comes_from_first :
    let roles : List AuthRole :=
      [⟨"council", false, [], .role⟩,
       ⟨"council", true, ["*:VoteApprove"], .token⟩]
    namedRoleAllows roles "council" "transfer" "VoteApprove" = true ∧
    firstRoleWeightKind roles "council" = some .role := by
  decide

theorem allowed_name_occurs_in_policy (roles : List AuthRole)
    (name kind action : String)
    (h : namedRoleAllows roles name kind action = true) :
    name ∈ roles.map AuthRole.name := by
  by_cases hm : name ∈ roles.map AuthRole.name
  · exact hm
  · have hn := no_name_no_matching_permissions roles name hm
    simp [namedRoleAllows, hn] at h

theorem canonical_allowed_name_iff (roles : List AuthRole)
    (name kind action : String) :
    name ∈ canonicalAllowedRoleNames roles kind action ↔
      namedRoleAllows roles name kind action = true := by
  constructor
  · intro h
    exact (List.mem_filter.mp h).2
  · intro h
    apply List.mem_filter.mpr
    exact ⟨List.mem_eraseDups.mpr (allowed_name_occurs_in_policy roles name kind action h), h⟩

theorem authorized_order_membership (roles : List AuthRole)
    (kind action : String) (selected : List String)
    (h : allowedRoleOrder roles kind action selected) (name : String) :
    name ∈ selected ↔ namedRoleAllows roles name kind action = true := by
  exact (List.Perm.mem_iff h).trans (canonical_allowed_name_iff roles name kind action)

theorem authorized_outcome_boolean (roles : List AuthRole)
    (kind action : String) (selected : List String) (allowed : Bool)
    (h : authorizationOutcome roles kind action selected allowed) :
    allowed = true ↔ ∃ name, name ∈ selected := by
  rcases h with ⟨_, ha⟩
  subst allowed
  cases selected with
  | nil => simp
  | cons name tail => simp

theorem authorized_outcome_member (roles : List AuthRole)
    (kind action : String) (selected : List String) (allowed : Bool)
    (h : authorizationOutcome roles kind action selected allowed) (name : String) :
    name ∈ selected ↔ namedRoleAllows roles name kind action = true := by
  exact authorized_order_membership roles kind action selected h.1 name

theorem duplicate_name_can_authorize_with_first_role_weight :
    let roles : List AuthRole :=
      [⟨"council", false, [], .role⟩,
       ⟨"council", true, ["*:VoteApprove"], .token⟩]
    canonicalAllowedRoleNames roles "vote" "VoteApprove" = ["council"] ∧
    firstRoleWeightKind roles "council" = some .role := by
  decide

theorem authorized_order_uniform_decision
    (roles : List AuthRole) (kind action : String)
    (selected : List String) (resolve : String → StatusRole)
    (submission period now supply : Nat) (decision : Decision)
    (horder : allowedRoleOrder roles kind action selected)
    (hnotexpired : now ≤ submission + period)
    (hdec : decision ≠ .inProgress)
    (hagree : ∀ d ∈
      (canonicalAllowedRoleNames roles kind action).map
        (fun name => roleDecision (resolve name) supply),
        d = .inProgress ∨ d = decision)
    (hpresent : decision ∈
      (canonicalAllowedRoleNames roles kind action).map
        (fun name => roleDecision (resolve name) supply)) :
    proposalStatusForRoles .inProgress submission period now supply
      (selected.map resolve) = some (decisionStatus decision) := by
  have hperm : List.Perm
      (selected.map (fun name => roleDecision (resolve name) supply))
      ((canonicalAllowedRoleNames roles kind action).map
          (fun name => roleDecision (resolve name) supply)) :=
    horder.map _
  have hagreeSelected : ∀ d ∈ selected.map
      (fun name => roleDecision (resolve name) supply),
      d = .inProgress ∨ d = decision := by
    intro d hd
    exact hagree d ((hperm.mem_iff).mp hd)
  have hpresentSelected : decision ∈ selected.map
      (fun name => roleDecision (resolve name) supply) :=
    (hperm.mem_iff).mpr hpresent
  have hfirst := first_decisive_consistent decision hdec
    (selected.map (fun name => roleDecision (resolve name) supply))
    hagreeSelected hpresentSelected
  have hfirst' : firstDecisive
      ((selected.map resolve).map (roleDecision · supply)) = decision := by
    simpa [List.map_map, Function.comp_def] using hfirst
  have hfirst'' : firstDecisive
      (selected.map ((roleDecision · supply) ∘ resolve)) = decision := by
    simpa [List.map_map, Function.comp_def] using hfirst'
  simp [proposalStatusForRoles, expired, Nat.not_lt.mpr hnotexpired,
    hfirst'', hdec]

end SputnikDAO2
