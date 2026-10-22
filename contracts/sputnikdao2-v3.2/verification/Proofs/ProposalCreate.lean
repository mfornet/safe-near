import Model.ProposalCreate

namespace SputnikDAO2

theorem valid_add_kind_policy_safe (stakingSet : Bool)
    (kind : ProposalKindCheck)
    (h : validAddKind stakingSet kind = true) :
    policyKindSafe kind := by
  cases kind <;> simp_all [validAddKind, policyKindSafe]

theorem policy_entries_safe_set_proposal
    (entries : List (Nat × CreatedProposal))
    (id : Nat) (proposal : CreatedProposal)
    (hentries : policyEntriesSafe entries)
    (hproposal : policyKindSafe proposal.kind) :
    policyEntriesSafe (setProposal entries id proposal) := by
  induction entries with
  | nil =>
      intro entry hmem
      simp [setProposal] at hmem
      rcases hmem with rfl
      exact hproposal
  | cons head rest ih =>
      obtain ⟨oldId, oldProposal⟩ := head
      by_cases hid : oldId = id
      · intro entry hmem
        simp [setProposal, hid] at hmem
        rcases hmem with hnew | hold
        · rcases hnew with rfl
          exact hproposal
        · exact hentries entry (by simp [hold])
      · have hrest : policyEntriesSafe rest := by
          intro entry hmem
          exact hentries entry (by simp [hmem])
        have htail := ih hrest
        intro entry hmem
        simp [setProposal, hid] at hmem
        rcases hmem with hhead | htailmem
        · exact hentries entry (by simp [hhead])
        · exact htail entry htailmem

theorem proposal_at_member
    (entries : List (Nat × CreatedProposal))
    (id : Nat) (proposal : CreatedProposal)
    (h : proposalAt entries id = some proposal) :
    (id, proposal) ∈ entries := by
  induction entries with
  | nil => simp [proposalAt] at h
  | cons head rest ih =>
      obtain ⟨oldId, oldProposal⟩ := head
      by_cases hid : oldId = id
      · subst oldId
        simp [proposalAt] at h
        cases h
        simp
      · simp [proposalAt, hid] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem policy_entries_safe_update_same_kind
    (entries : List (Nat × CreatedProposal))
    (id : Nat) (old updated : CreatedProposal)
    (hentries : policyEntriesSafe entries)
    (hlookup : proposalAt entries id = some old)
    (hkind : updated.kind = old.kind) :
    policyEntriesSafe (setProposal entries id updated) := by
  have hold : policyKindSafe old.kind :=
    hentries (id, old) (proposal_at_member entries id old hlookup)
  apply policy_entries_safe_set_proposal entries id updated hentries
  simpa [hkind] using hold

theorem proposal_at_set_proposal (entries : List (Nat × CreatedProposal))
    (id : Nat) (proposal : CreatedProposal) :
    proposalAt (setProposal entries id proposal) id = some proposal := by
  induction entries with
  | nil => simp [setProposal, proposalAt]
  | cons entry rest ih =>
      obtain ⟨oldId, oldProposal⟩ := entry
      by_cases h : oldId = id
      · subst oldId
        simp [setProposal, proposalAt]
      · simp [setProposal, proposalAt, h, ih]

theorem wrong_bond_aborts_add (state : ProposalCreateState)
    (ctx : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (h : ctx.attached ≠ ctx.policyBond) :
    addProposal state ctx kind description = none := by
  simp [addProposal, h]

theorem invalid_kind_aborts_add (state : ProposalCreateState)
    (ctx : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (h : validAddKind state.stakingSet kind = false) :
    addProposal state ctx kind description = none := by
  by_cases hb : ctx.attached = ctx.policyBond
  · simp [addProposal, hb, h]
  · simp [addProposal, hb]

theorem no_permission_aborts_add (state : ProposalCreateState)
    (ctx : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (h : ctx.addPermission = false) :
    addProposal state ctx kind description = none := by
  by_cases hb : ctx.attached = ctx.policyBond
  · by_cases hk : validAddKind state.stakingSet kind = true
    · simp [addProposal, hb, hk, h]
    · simp [addProposal, hb, hk]
  · simp [addProposal, hb]

theorem full_proposal_id_aborts_add (state : ProposalCreateState)
    (ctx : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (h : maxU64 ≤ state.lastId) :
    addProposal state ctx kind description = none := by
  by_cases hb : ctx.attached = ctx.policyBond
  · by_cases hk : validAddKind state.stakingSet kind = true
    · by_cases hp : ctx.addPermission = true
      · simp [addProposal, hb, hk, hp, h]
      · simp [addProposal, hb, hk, hp]
    · simp [addProposal, hb, hk]
  · simp [addProposal, hb]

theorem add_proposal_success_effect (state : ProposalCreateState)
    (ctx : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String)
    (hbond : ctx.attached = ctx.policyBond)
    (hkind : validAddKind state.stakingSet kind = true)
    (hpermission : ctx.addPermission = true)
    (hroom : state.lastId < maxU64) :
    ∃ next,
      addProposal state ctx kind description = some (next, state.lastId) ∧
      next.lastId = state.lastId + 1 ∧
      next.locked = min (state.locked + ctx.attached) maxU128 ∧
      proposalAt next.proposals state.lastId =
        some ⟨ctx.predecessor, description, kind, .inProgress,
          ctx.blockTimestamp, [], [], [ctx.blockHeight]⟩ ∧
      next.actionsLog = appendLog20 state.actionsLog
        ⟨ctx.predecessor, state.lastId, ctx.blockHeight⟩ := by
  let proposal : CreatedProposal :=
    ⟨ctx.predecessor, description, kind, .inProgress,
      ctx.blockTimestamp, [], [], [ctx.blockHeight]⟩
  let next : ProposalCreateState :=
    ⟨state.lastId + 1,
      min (state.locked + ctx.attached) maxU128,
      state.stakingSet,
      setProposal state.proposals state.lastId proposal,
      appendLog20 state.actionsLog
        ⟨ctx.predecessor, state.lastId, ctx.blockHeight⟩⟩
  refine ⟨next, ?_, rfl, rfl, ?_, rfl⟩
  · simp [addProposal, hbond, hkind, hpermission,
      Nat.not_le.mpr hroom, next, proposal]
  · exact proposal_at_set_proposal state.proposals state.lastId proposal

theorem add_proposal_preserves_policy_entries
    (state : ProposalCreateState) (ctx : ProposalCreateContext)
    (kind : ProposalKindCheck) (description : String)
    (hentries : policyEntriesSafe state.proposals)
    (hbond : ctx.attached = ctx.policyBond)
    (hkind : validAddKind state.stakingSet kind = true)
    (hpermission : ctx.addPermission = true)
    (hroom : state.lastId < maxU64) :
    ∃ next,
      addProposal state ctx kind description = some (next, state.lastId) ∧
      policyEntriesSafe next.proposals := by
  let proposal : CreatedProposal :=
    ⟨ctx.predecessor, description, kind, .inProgress,
      ctx.blockTimestamp, [], [], [ctx.blockHeight]⟩
  let next : ProposalCreateState :=
    ⟨state.lastId + 1,
      min (state.locked + ctx.attached) maxU128,
      state.stakingSet,
      setProposal state.proposals state.lastId proposal,
      appendLog20 state.actionsLog
        ⟨ctx.predecessor, state.lastId, ctx.blockHeight⟩⟩
  refine ⟨next, ?_, ?_⟩
  · simp [addProposal, hbond, hkind, hpermission,
      Nat.not_le.mpr hroom, next, proposal]
  · exact policy_entries_safe_set_proposal state.proposals state.lastId
      proposal hentries (valid_add_kind_policy_safe state.stakingSet kind hkind)

theorem base_token_message_is_invalid (stakingSet : Bool) :
    validAddKind stakingSet (.transfer true true) = false := by
  simp [validAddKind]

theorem staking_change_rejected_when_set :
    validAddKind true .setStakingContract = false := by
  decide

theorem legacy_policy_version_rejected (stakingSet : Bool) :
    validAddKind stakingSet (.changePolicy false) = false := by
  simp [validAddKind]

theorem append_log20_full_drops_oldest {α : Type} (entries : List α)
    (entry : α) (h : 20 ≤ entries.length) :
    appendLog20 entries entry = entries.drop 1 ++ [entry] := by
  simp [appendLog20, h]

theorem append_log20_short_appends {α : Type} (entries : List α)
    (entry : α) (h : entries.length < 20) :
    appendLog20 entries entry = entries ++ [entry] := by
  simp [appendLog20, Nat.not_le.mpr h]

end SputnikDAO2
