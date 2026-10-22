import Model.CallbackExport
import Proofs.BlobKeySeparation

namespace SputnikDAO2

theorem ordinary_callback_rejects_external_caller
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option TransferCallbackState)
    (proposalId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (hcaller : ctx.current ≠ ctx.predecessor) :
    runOrdinaryCallbackExport raw ctx state proposalId resultCount
      result policy encodeProposal encodeRoot = none := by
  simp [runOrdinaryCallbackExport, finishTransferCallback, hcaller]

theorem ordinary_callback_requires_one_result
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option TransferCallbackState)
    (proposalId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (hcount : resultCount ≠ 1) :
    runOrdinaryCallbackExport raw ctx state proposalId resultCount
      result policy encodeProposal encodeRoot = none := by
  simp [runOrdinaryCallbackExport, finishTransferCallback, hcount]

theorem ordinary_callback_success_writes_proposal_and_root
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : TransferCallbackState)
    (proposalId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (after : TransferCallbackResult)
    (h : runOrdinaryCallbackExport raw ctx (some state)
      proposalId resultCount result policy encodeProposal encodeRoot =
      some (final, after)) :
    proposalId < 256 ^ 8 ∧
    finishTransferCallback state (ctx.current == ctx.predecessor)
      resultCount result policy = some after ∧
    final (daoProposalEntryKey proposalId) =
      some (encodeProposal after) ∧
    final daoRootKey = some (encodeRoot after) := by
  have hi : findDAOExport "on_proposal_callback" =
      some ⟨"on_proposal_callback", .call, false, true⟩ := by decide
  by_cases hid : proposalId < 256 ^ 8
  · cases hf : finishTransferCallback state
        (ctx.current == ctx.predecessor) resultCount result policy with
    | none => simp [runOrdinaryCallbackExport, hf] at h
    | some computed =>
        by_cases hcaller : ctx.current = ctx.predecessor
        · have hftrue : finishTransferCallback state true resultCount
              result policy = some computed := by
            simpa [hcaller] using hf
          by_cases hdeposit : ctx.attachedDeposit = 0
          · by_cases hargs : ctx.argumentsDecoded = true
            · simp [runOrdinaryCallbackExport, hftrue,
                runGeneratedCallWrapper, hi, hcaller,
                hdeposit, hargs] at h
              rcases h with ⟨_, ⟨hfinalEq, hafterEq⟩⟩
              subst final
              subst after
              have hkey : daoProposalEntryKey proposalId ≠ daoRootKey := by
                intro heq
                have hlength := congrArg List.length heq
                simp [dao_proposal_key_length, daoRootKey] at hlength
              refine ⟨hid, rfl, ?_, ?_⟩
              · simp [bountyRawWrite, hkey]
              · simp [bountyRawWrite]
            · simp [runOrdinaryCallbackExport,
                runGeneratedCallWrapper, hi, hargs] at h
          · simp [runOrdinaryCallbackExport,
              runGeneratedCallWrapper, hi, hdeposit] at h
        · simp [runOrdinaryCallbackExport,
            runGeneratedCallWrapper, hi, hcaller] at h
  · simp [runOrdinaryCallbackExport, hid] at h

theorem ordinary_callback_success_requires_context
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : TransferCallbackState)
    (proposalId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (after : TransferCallbackResult)
    (h : runOrdinaryCallbackExport raw ctx (some state)
      proposalId resultCount result policy encodeProposal encodeRoot =
      some (final, after)) :
    state.proposalPresent = true ∧
      ctx.current = ctx.predecessor ∧ resultCount = 1 := by
  have hbody :=
    (ordinary_callback_success_writes_proposal_and_root raw final ctx
      state proposalId resultCount result policy encodeProposal
      encodeRoot after h).2.1
  by_cases hpresent : state.proposalPresent = true
  · by_cases hcaller : ctx.current = ctx.predecessor
    · by_cases hcount : resultCount = 1
      · exact ⟨hpresent, hcaller, hcount⟩
      · simp [finishTransferCallback, hcount] at hbody
    · simp [finishTransferCallback, hcaller] at hbody
  · simp [finishTransferCallback, hpresent] at hbody

theorem ordinary_failed_callback_keeps_lock
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : TransferCallbackState)
    (proposalId resultCount : Nat)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (after : TransferCallbackResult)
    (h : runOrdinaryCallbackExport raw ctx (some state)
      proposalId resultCount .failure policy encodeProposal encodeRoot =
      some (final, after)) :
    after = ⟨.failed, state.locked, none⟩ := by
  obtain ⟨hpresent, hcaller, hcount⟩ :=
    ordinary_callback_success_requires_context raw final ctx state
      proposalId resultCount .failure policy encodeProposal encodeRoot
      after h
  have hbody :=
    (ordinary_callback_success_writes_proposal_and_root raw final ctx
      state proposalId resultCount .failure policy encodeProposal
      encodeRoot after h).2.1
  simp [finishTransferCallback, hpresent, hcaller, hcount] at hbody
  exact hbody.symm

theorem ordinary_successful_callback_uses_current_bond
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : TransferCallbackState)
    (proposalId resultCount : Nat)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : TransferCallbackResult → BountyBytes)
    (after : TransferCallbackResult)
    (h : runOrdinaryCallbackExport raw ctx (some state)
      proposalId resultCount .success policy encodeProposal encodeRoot =
      some (final, after)) :
    after = ⟨.approved, state.locked - policy.proposalBond,
      some ⟨state.proposer, policy.proposalBond⟩⟩ := by
  obtain ⟨hpresent, hcaller, hcount⟩ :=
    ordinary_callback_success_requires_context raw final ctx state
      proposalId resultCount .success policy encodeProposal encodeRoot
      after h
  have hbody :=
    (ordinary_callback_success_writes_proposal_and_root raw final ctx
      state proposalId resultCount .success policy encodeProposal
      encodeRoot after h).2.1
  simp [finishTransferCallback, hpresent, hcaller, hcount,
    returnProposalBonds] at hbody
  exact hbody.symm

end SputnikDAO2
