import Model.ProposalAct

namespace SputnikDAO2

theorem policy_entries_safe_erase
    (entries : List (Nat × CreatedProposal)) (id : Nat)
    (hentries : policyEntriesSafe entries) :
    policyEntriesSafe (eraseProposal entries id) := by
  intro entry hmem
  exact hentries entry ((List.mem_filter.mp hmem).1)

theorem act_non_vote_preserves_policy_entries
    (state : NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (action : NonVoteAction) (next : NonVoteState)
    (hentries : policyEntriesSafe state.proposals)
    (h : actNonVote state ctx id action = some next) :
    policyEntriesSafe next.proposals := by
  unfold actNonVote at h
  cases hlookup : proposalAt state.proposals id with
  | none => simp [hlookup] at h
  | some stored =>
      simp only [hlookup] at h
      cases hp : ctx.permissionAllowed <;> simp [hp] at h
      cases hk : ctx.exactKindMatches <;> simp [hk] at h
      cases action with
      | addProposal => simp at h
      | removeProposal =>
          simp at h
          cases h
          exact policy_entries_safe_erase state.proposals id hentries
      | moveToHub =>
          simp at h
          cases h
          exact hentries

theorem erased_proposal_is_absent (entries : List (Nat × CreatedProposal))
    (id : Nat) :
    proposalAt (eraseProposal entries id) id = none := by
  induction entries with
  | nil => simp [eraseProposal, proposalAt]
  | cons entry rest ih =>
      obtain ⟨oldId, proposal⟩ := entry
      by_cases h : oldId = id
      · subst oldId
        simpa [eraseProposal, proposalAt] using ih
      · simpa [eraseProposal, proposalAt, h] using ih

theorem missing_proposal_aborts (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (action : NonVoteAction)
    (h : proposalAt state.proposals id = none) :
    actNonVote state ctx id action = none := by
  simp [actNonVote, h]

theorem denied_action_rolls_back_log (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (action : NonVoteAction)
    (h : ctx.permissionAllowed = false) :
    actNonVote state ctx id action = none := by
  cases hlookup : proposalAt state.proposals id with
  | none => simp [actNonVote, hlookup]
  | some proposal => simp [actNonVote, hlookup, h]

theorem wrong_kind_rolls_back_log (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (action : NonVoteAction)
    (h : ctx.exactKindMatches = false) :
    actNonVote state ctx id action = none := by
  cases hlookup : proposalAt state.proposals id with
  | none => simp [actNonVote, hlookup]
  | some proposal =>
      cases hp : ctx.permissionAllowed <;>
        simp [actNonVote, hlookup, hp, h]

theorem add_proposal_is_wrong_act_action (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) :
    actNonVote state ctx id .addProposal = none := by
  cases hlookup : proposalAt state.proposals id with
  | none => simp [actNonVote, hlookup]
  | some proposal =>
      cases hp : ctx.permissionAllowed <;>
        cases hk : ctx.exactKindMatches <;>
          simp [actNonVote, hlookup, hp, hk]

theorem remove_proposal_effect (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (stored : CreatedProposal)
    (hlookup : proposalAt state.proposals id = some stored)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true) :
    actNonVote state ctx id .removeProposal =
      some ⟨eraseProposal state.proposals id,
        appendLog20 state.globalLog
          ⟨ctx.predecessor, id, .removeProposal, ctx.blockHeight⟩,
        state.locked⟩ := by
  simp [actNonVote, hlookup, hpermission, hkind]

theorem remove_proposal_deletes_without_unlocking (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (stored : CreatedProposal)
    (hlookup : proposalAt state.proposals id = some stored)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true) :
    ∃ next,
      actNonVote state ctx id .removeProposal = some next ∧
      proposalAt next.proposals id = none ∧
      next.locked = state.locked := by
  refine ⟨⟨eraseProposal state.proposals id,
    appendLog20 state.globalLog
      ⟨ctx.predecessor, id, .removeProposal, ctx.blockHeight⟩,
    state.locked⟩, ?_, ?_, rfl⟩
  · exact remove_proposal_effect state ctx id stored hlookup hpermission hkind
  · exact erased_proposal_is_absent state.proposals id

theorem move_to_hub_keeps_stored_proposal (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (stored : CreatedProposal)
    (hlookup : proposalAt state.proposals id = some stored)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true) :
    actNonVote state ctx id .moveToHub =
      some ⟨state.proposals,
        appendLog20 state.globalLog
          ⟨ctx.predecessor, id, .moveToHub, ctx.blockHeight⟩,
        state.locked⟩ := by
  simp [actNonVote, hlookup, hpermission, hkind]

theorem move_to_hub_preserves_status_and_lock (state : NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (stored : CreatedProposal)
    (hlookup : proposalAt state.proposals id = some stored)
    (hpermission : ctx.permissionAllowed = true)
    (hkind : ctx.exactKindMatches = true) :
    ∃ next,
      actNonVote state ctx id .moveToHub = some next ∧
      proposalAt next.proposals id = some stored ∧
      next.locked = state.locked := by
  refine ⟨⟨state.proposals,
    appendLog20 state.globalLog
      ⟨ctx.predecessor, id, .moveToHub, ctx.blockHeight⟩,
    state.locked⟩, ?_, hlookup, rfl⟩
  exact move_to_hub_keeps_stored_proposal state ctx id stored
    hlookup hpermission hkind

end SputnikDAO2
