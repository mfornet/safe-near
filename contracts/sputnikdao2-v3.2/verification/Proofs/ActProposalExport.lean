import Model.ActProposalExport
import Proofs.ExportWrapper

namespace SputnikDAO2

theorem act_nonvote_export_requires_policy
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes) :
    runActNonVoteExport raw wrapper state ctx false id action
      encodeRoot = none := by
  simp [runActNonVoteExport]

theorem act_nonvote_export_rejects_out_of_range_id
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option NonVoteState) (ctx : NonVoteContext)
    (policyReadable : Bool) (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes)
    (hid : maxU64 < id) :
    runActNonVoteExport raw wrapper state ctx policyReadable id action
      encodeRoot = none := by
  simp [runActNonVoteExport, hid]

theorem act_nonvote_export_nonpayable
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option NonVoteState) (ctx : NonVoteContext)
    (policyReadable : Bool) (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes)
    (hdeposit : wrapper.attachedDeposit ≠ 0) :
    runActNonVoteExport raw wrapper state ctx policyReadable id action
      encodeRoot = none := by
  have hi : findDAOExport "act_proposal" =
      some ⟨"act_proposal", .call, false, false⟩ := by decide
  cases state with
  | none => simp [runActNonVoteExport]
  | some before =>
      by_cases hid : id ≤ maxU64
      · cases policyReadable with
        | false => simp [runActNonVoteExport]
        | true =>
            cases hstep : actNonVote before
                ⟨wrapper.predecessor, ctx.blockHeight,
                  ctx.permissionAllowed, ctx.exactKindMatches⟩ id action with
            | none => simp [runActNonVoteExport, hstep]
            | some after =>
                simp [runActNonVoteExport,
                  runGeneratedCallWrapper, hi, hdeposit]
      · simp [runActNonVoteExport, Nat.not_le.mp hid]

theorem act_nonvote_export_add_action_aborts
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option NonVoteState) (ctx : NonVoteContext)
    (policyReadable : Bool) (id : Nat)
    (encodeRoot : NonVoteState → BountyBytes) :
    runActNonVoteExport raw wrapper state ctx policyReadable id
      .addProposal encodeRoot = none := by
  cases state with
  | none => simp [runActNonVoteExport]
  | some before =>
      cases hlookup : proposalAt before.proposals id with
      | none =>
          simp [runActNonVoteExport, actNonVote, hlookup]
      | some proposal =>
          simp [runActNonVoteExport, actNonVote, hlookup]

theorem act_nonvote_export_success_body
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes)
    (h : runActNonVoteExport raw wrapper (some state) ctx true id
      action encodeRoot = some final) :
    ∃ after,
      actNonVote state
        ⟨wrapper.predecessor, ctx.blockHeight,
          ctx.permissionAllowed, ctx.exactKindMatches⟩
        id action = some after ∧
      final = bountyRawWrite (nonVoteRawEffect raw id action)
        daoRootKey (encodeRoot after) := by
  let bodyCtx : NonVoteContext :=
    ⟨wrapper.predecessor, ctx.blockHeight,
      ctx.permissionAllowed, ctx.exactKindMatches⟩
  cases hstep : actNonVote state bodyCtx id action with
  | none => simp [runActNonVoteExport, bodyCtx, hstep] at h
  | some after =>
      have hw : runGeneratedCallWrapper raw "act_proposal"
          { wrapper with stateDecoded := true }
          (some (nonVoteRawEffect raw id action, encodeRoot after)) =
          some final := by
        have hs : id ≤ maxU64 ∧
            runGeneratedCallWrapper raw "act_proposal"
              { wrapper with stateDecoded := true }
              (some (nonVoteRawEffect raw id action, encodeRoot after)) =
              some final := by
          simpa [runActNonVoteExport, bodyCtx, hstep] using h
        exact hs.2
      have hfinal := generated_call_success_is_root_write raw
        (nonVoteRawEffect raw id action)
        final "act_proposal" { wrapper with stateDecoded := true }
        (encodeRoot after) hw
      exact ⟨after, rfl, hfinal⟩

theorem act_nonvote_remove_export_deletes_proposal_key
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (encodeRoot : NonVoteState → BountyBytes)
    (h : runActNonVoteExport raw wrapper (some state) ctx true id
      .removeProposal encodeRoot = some final) :
    final (daoProposalEntryKey id) = none := by
  obtain ⟨after, _, hfinal⟩ :=
    act_nonvote_export_success_body raw final wrapper state ctx id
      .removeProposal encodeRoot h
  rw [hfinal]
  simp [nonVoteRawEffect, bountyRawWrite, bountyRawRemove,
    daoProposalEntryKey, daoRootKey]

theorem act_nonvote_move_export_keeps_proposal_key
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : NonVoteState) (ctx : NonVoteContext)
    (id : Nat) (encodeRoot : NonVoteState → BountyBytes)
    (h : runActNonVoteExport raw wrapper (some state) ctx true id
      .moveToHub encodeRoot = some final) :
    final (daoProposalEntryKey id) = raw (daoProposalEntryKey id) := by
  obtain ⟨after, _, hfinal⟩ :=
    act_nonvote_export_success_body raw final wrapper state ctx id
      .moveToHub encodeRoot h
  rw [hfinal]
  simp [nonVoteRawEffect, bountyRawWrite, daoProposalEntryKey, daoRootKey]

end SputnikDAO2
