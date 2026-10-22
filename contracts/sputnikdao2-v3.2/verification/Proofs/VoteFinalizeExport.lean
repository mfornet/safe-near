import Model.VoteFinalizeExport
import Proofs.ExportWrapper

namespace SputnikDAO2

theorem vote_finalize_returns_current_policy_bond
    (state : VoteFinalizeState) (ctx : FinalizeContext)
    (account : String) (id height : Nat)
    (policy : BondPolicyAmounts) (result : VoteFinalizeResult)
    (h : runVoteFinalize state ctx account id height policy =
      some result) :
    result.locked = state.locked - policy.proposalBond ∧
      result.detachedRefund = ⟨state.proposer, policy.proposalBond⟩ := by
  cases hp : selectFinalize { ctx with
      proposalExists := state.proposalPresent,
      originalStatus := state.status } with
  | none => simp [runVoteFinalize, hp] at h
  | some plan =>
      simp [runVoteFinalize, hp, returnProposalBonds] at h
      subst result
      simp

theorem vote_finalize_export_requires_proposal_key
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option VoteFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : VoteFinalizeResult → BountyBytes)
    (hkey : raw (daoProposalEntryKey id) = none) :
    runVoteFinalizeExport raw wrapper state ctx id height policyReadable
      storedKindIsVote storedDecoded policy encodeProposal encodeRoot =
      none := by
  cases state with
  | none => simp [runVoteFinalizeExport]
  | some before => simp [runVoteFinalizeExport, hkey]

theorem vote_finalize_export_rejects_time_overflow
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option VoteFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : VoteFinalizeResult → BountyBytes)
    (hoverflow : maxU64 < ctx.submission + ctx.period) :
    runVoteFinalizeExport raw wrapper state ctx id height policyReadable
      storedKindIsVote storedDecoded policy encodeProposal encodeRoot =
      none := by
  simp [runVoteFinalizeExport, hoverflow]

theorem vote_finalize_export_nonpayable
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option VoteFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : VoteFinalizeResult → BountyBytes)
    (hdeposit : wrapper.attachedDeposit ≠ 0) :
    runVoteFinalizeExport raw wrapper state ctx id height policyReadable
      storedKindIsVote storedDecoded policy encodeProposal encodeRoot =
      none := by
  have hi : findDAOExport "act_proposal" =
      some ⟨"act_proposal", .call, false, false⟩ := by decide
  cases state with
  | none => simp [runVoteFinalizeExport]
  | some before =>
      simp [runVoteFinalizeExport, runGeneratedCallWrapper, hi,
        hdeposit]

theorem vote_finalize_export_success_body
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : VoteFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : VoteFinalizeResult → BountyBytes)
    (result : VoteFinalizeResult)
    (h : runVoteFinalizeExport raw wrapper (some state) ctx id height
      policyReadable storedKindIsVote storedDecoded policy encodeProposal
      encodeRoot = some (final, result)) :
    runVoteFinalize state ctx wrapper.predecessor id height policy =
      some result ∧
    final = bountyRawWrite
      (bountyRawWrite raw (daoProposalEntryKey id)
        (encodeProposal result)) daoRootKey (encodeRoot result) := by
  cases hkey : raw (daoProposalEntryKey id) with
  | none => simp [runVoteFinalizeExport, hkey] at h
  | some old =>
      cases hstep : runVoteFinalize state ctx wrapper.predecessor id
          height policy with
      | none => simp [runVoteFinalizeExport, hkey, hstep] at h
      | some actual =>
          cases hw : runGeneratedCallWrapper raw "act_proposal"
              { wrapper with stateDecoded := true }
              (some (bountyRawWrite raw (daoProposalEntryKey id)
                (encodeProposal actual), encodeRoot actual)) with
          | none =>
              simp [runVoteFinalizeExport, hkey, hstep, hw] at h
          | some produced =>
              simp [runVoteFinalizeExport, hkey, hstep, hw] at h
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfinal,
                hresult⟩ := h
              subst final
              have hwrite := generated_call_success_is_root_write raw
                (bountyRawWrite raw (daoProposalEntryKey id)
                  (encodeProposal result))
                produced "act_proposal" { wrapper with stateDecoded := true }
                (encodeRoot result) hw
              exact ⟨rfl, hwrite⟩

theorem vote_finalize_export_writes_proposal_and_root
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : VoteFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : VoteFinalizeResult → BountyBytes)
    (result : VoteFinalizeResult)
    (h : runVoteFinalizeExport raw wrapper (some state) ctx id height
      policyReadable storedKindIsVote storedDecoded policy encodeProposal
      encodeRoot = some (final, result)) :
    final (daoProposalEntryKey id) = some (encodeProposal result) ∧
      final daoRootKey = some (encodeRoot result) := by
  have hfinal := (vote_finalize_export_success_body raw final wrapper state
    ctx id height policyReadable storedKindIsVote storedDecoded policy
    encodeProposal encodeRoot result h).2
  rw [hfinal]
  constructor
  · simp [bountyRawWrite, daoProposalEntryKey, daoRootKey]
  · simp [bountyRawWrite]

end SputnikDAO2
