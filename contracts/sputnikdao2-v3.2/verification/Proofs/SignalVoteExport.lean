import Model.SignalVoteExport
import Proofs.ExportWrapper

namespace SputnikDAO2

theorem signal_vote_export_rejects_non_vote_kind
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option SignalVoteState) (ctx : SignalVoteContext)
    (id : Nat) (policyReadable storedDecoded : Bool)
    (encodeProposal encodeRoot : SignalVoteResult → BountyBytes) :
    runSignalVoteExport raw wrapper state ctx id policyReadable false
      storedDecoded encodeProposal encodeRoot = none := by
  simp [runSignalVoteExport]

theorem signal_vote_export_requires_proposal_key
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option SignalVoteState) (ctx : SignalVoteContext)
    (id : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (encodeProposal encodeRoot : SignalVoteResult → BountyBytes)
    (hkey : raw (daoProposalEntryKey id) = none) :
    runSignalVoteExport raw wrapper state ctx id policyReadable
      storedKindIsVote storedDecoded encodeProposal encodeRoot = none := by
  cases state with
  | none => simp [runSignalVoteExport]
  | some before =>
      simp [runSignalVoteExport, hkey]

theorem signal_vote_export_success_body
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : SignalVoteState) (ctx : SignalVoteContext)
    (id : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (encodeProposal encodeRoot : SignalVoteResult → BountyBytes)
    (result : SignalVoteResult)
    (h : runSignalVoteExport raw wrapper (some state) ctx id
      policyReadable storedKindIsVote storedDecoded encodeProposal
      encodeRoot = some (final, result)) :
    runSignalVote state
      { ctx with account := wrapper.predecessor, proposalId := id } =
        some result ∧
    final = bountyRawWrite
      (signalVoteRawEffect raw id result encodeProposal)
      daoRootKey (encodeRoot result) := by
  let bodyCtx : SignalVoteContext :=
    { ctx with account := wrapper.predecessor, proposalId := id }
  cases hkey : raw (daoProposalEntryKey id) with
  | none => simp [runSignalVoteExport, hkey] at h
  | some old =>
      cases hstep : runSignalVote state bodyCtx with
      | none =>
          simp [runSignalVoteExport, bodyCtx, hkey, hstep] at h
      | some actual =>
          cases hw : runGeneratedCallWrapper raw "act_proposal"
              { wrapper with stateDecoded := true }
              (some (signalVoteRawEffect raw id actual encodeProposal,
                encodeRoot actual)) with
          | none =>
              simp [runSignalVoteExport, bodyCtx, hkey, hstep, hw] at h
          | some produced =>
              simp [runSignalVoteExport, bodyCtx, hkey, hstep, hw] at h
              obtain ⟨_, _, _, _, hfinal, hresult⟩ := h
              subst final
              have hwrite := generated_call_success_is_root_write raw
                (signalVoteRawEffect raw id result encodeProposal)
                produced "act_proposal" { wrapper with stateDecoded := true }
                (encodeRoot result) hw
              exact ⟨rfl, hwrite⟩

theorem signal_vote_export_removed_deletes_key
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : SignalVoteState) (ctx : SignalVoteContext)
    (id : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (encodeProposal encodeRoot : SignalVoteResult → BountyBytes)
    (result : SignalVoteResult)
    (h : runSignalVoteExport raw wrapper (some state) ctx id
      policyReadable storedKindIsVote storedDecoded encodeProposal
      encodeRoot = some (final, result))
    (hremoved : result.effect = .deleteProposal) :
    final (daoProposalEntryKey id) = none := by
  have hbody := (signal_vote_export_success_body raw final wrapper state
    ctx id policyReadable storedKindIsVote storedDecoded encodeProposal
    encodeRoot result h).2
  rw [hbody]
  simp [signalVoteRawEffect, hremoved, bountyRawWrite, bountyRawRemove,
    daoProposalEntryKey, daoRootKey]

theorem signal_vote_export_stored_writes_key
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : SignalVoteState) (ctx : SignalVoteContext)
    (id : Nat) (policyReadable storedKindIsVote storedDecoded : Bool)
    (encodeProposal encodeRoot : SignalVoteResult → BountyBytes)
    (result : SignalVoteResult)
    (h : runSignalVoteExport raw wrapper (some state) ctx id
      policyReadable storedKindIsVote storedDecoded encodeProposal
      encodeRoot = some (final, result))
    (hstore : result.effect ≠ .deleteProposal) :
    final (daoProposalEntryKey id) = some (encodeProposal result) := by
  have hbody := (signal_vote_export_success_body raw final wrapper state
    ctx id policyReadable storedKindIsVote storedDecoded encodeProposal
    encodeRoot result h).2
  rw [hbody]
  cases heffect : result.effect <;>
    simp_all [signalVoteRawEffect, bountyRawWrite,
      daoProposalEntryKey, daoRootKey]

end SputnikDAO2
