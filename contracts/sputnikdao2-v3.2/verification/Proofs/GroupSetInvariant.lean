import Model.RoleMutation

namespace SputnikDAO2

theorem insert_group_member_preserves_nodup
    (members : List String) (member : String)
    (h : members.Nodup) :
    (insertGroupMember members member).Nodup := by
  unfold insertGroupMember
  by_cases hm : member ∈ members
  · simp [hm, h]
  · simp [hm, List.nodup_append, h]
    intro a ha heq
    subst a
    exact hm ha

theorem delete_group_member_preserves_nodup
    (members : List String) (member : String)
    (h : members.Nodup) :
    (deleteGroupMember members member).Nodup := by
  exact h.filter _

theorem canonical_mutable_cons_iff (role : MutableRole)
    (rest : List MutableRole) :
    canonicalMutableRoles (role :: rest) ↔
      canonicalMutableRole role ∧ canonicalMutableRoles rest := by
  simp [canonicalMutableRoles]

theorem replace_or_append_preserves_canonical_groups
    (roles : List MutableRole) (replacement : MutableRole)
    (hroles : canonicalMutableRoles roles)
    (hreplacement : canonicalMutableRole replacement) :
    canonicalMutableRoles (replaceOrAppendRole roles replacement).1 := by
  induction roles with
  | nil => simpa [replaceOrAppendRole, canonicalMutableRoles]
      using hreplacement
  | cons old rest ih =>
      have hrest := (canonical_mutable_cons_iff old rest).mp hroles |>.2
      by_cases heq : old.name = replacement.name
      · simpa [replaceOrAppendRole, heq, canonical_mutable_cons_iff]
          using And.intro hreplacement hrest
      · have hnext := ih hrest
        cases hpair : replaceOrAppendRole rest replacement with
        | mk next effect =>
            simp [hpair] at hnext
            simpa [replaceOrAppendRole, heq, hpair,
              canonical_mutable_cons_iff] using
              And.intro ((canonical_mutable_cons_iff old rest).mp hroles).1 hnext

theorem remove_first_preserves_canonical_groups
    (roles : List MutableRole) (name : String)
    (hroles : canonicalMutableRoles roles) :
    canonicalMutableRoles (removeFirstRole roles name).1 := by
  induction roles with
  | nil => simp [removeFirstRole, canonicalMutableRoles]
  | cons old rest ih =>
      have hparts := (canonical_mutable_cons_iff old rest).mp hroles
      by_cases heq : old.name = name
      · simpa [removeFirstRole, heq] using hparts.2
      · have hnext := ih hparts.2
        cases hpair : removeFirstRole rest name with
        | mk next effect =>
            simp [hpair] at hnext
            simpa [removeFirstRole, heq, hpair,
              canonical_mutable_cons_iff] using And.intro hparts.1 hnext

theorem change_first_member_preserves_canonical_groups
    (roles : List MutableRole) (name member : String) (add : Bool)
    (hroles : canonicalMutableRoles roles) :
    canonicalMutableRoles
      (changeFirstMember roles name member add).1 := by
  induction roles with
  | nil => simp [changeFirstMember, canonicalMutableRoles]
  | cons old rest ih =>
      have hparts := (canonical_mutable_cons_iff old rest).mp hroles
      by_cases heq : old.name = name
      · cases hshape : old.shape with
        | everyone =>
            simpa [changeFirstMember, heq, hshape] using hroles
        | member threshold =>
            simpa [changeFirstMember, heq, hshape] using hroles
        | group members =>
            have hmembers : members.Nodup := by
              simpa [canonicalMutableRole, hshape] using hparts.1
            have hnext :
                (if add then insertGroupMember members member
                  else deleteGroupMember members member).Nodup := by
              cases add
              · simpa using delete_group_member_preserves_nodup
                  members member hmembers
              · simpa using insert_group_member_preserves_nodup
                  members member hmembers
            simpa [changeFirstMember, heq, hshape,
              canonical_mutable_cons_iff, canonicalMutableRole]
              using And.intro hnext hparts.2
      · have htail := ih hparts.2
        cases hpair : changeFirstMember rest name member add with
        | mk next effect =>
            simp [hpair] at htail
            simpa [changeFirstMember, heq, hpair,
              canonical_mutable_cons_iff] using And.intro hparts.1 htail

theorem role_mutations_preserve_canonical_groups
    (policy : MutablePolicyImage) (action : RoleMutationAction)
    (hpolicy : canonicalMutableRoles policy.roles)
    (haction : canonicalRoleMutationAction action) :
    canonicalMutableRoles (mutatePolicy policy action).1.roles := by
  cases action with
  | addOrUpdate replacement =>
      exact replace_or_append_preserves_canonical_groups
        policy.roles replacement hpolicy haction
  | remove name =>
      exact remove_first_preserves_canonical_groups
        policy.roles name hpolicy
  | addMember name member =>
      exact change_first_member_preserves_canonical_groups
        policy.roles name member true hpolicy
  | removeMember name member =>
      exact change_first_member_preserves_canonical_groups
        policy.roles name member false hpolicy
  | updateDefaultVotePolicy tag =>
      simpa [mutatePolicy] using hpolicy

end SputnikDAO2
