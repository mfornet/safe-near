import Model.BountyCallbackExport
import Proofs.CallbackExport
import Proofs.ExportWrapper

namespace SputnikDAO2

theorem bounty_callback_rejects_external_caller
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyResolutionState)
    (proposalPresent : Bool) (proposalId bountyId resultCount : Nat)
    (result : CallbackResult) (policy : BondPolicyAmounts)
    (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (hcaller : ctx.current ≠ ctx.predecessor) :
    runBountyCallbackExport raw ctx state proposalPresent proposalId
      bountyId resultCount result policy proposer encodeBounty
      encodeProposal encodeRoot = none := by
  simp [runBountyCallbackExport, finishBountyPayout, hcaller]

theorem bounty_callback_requires_one_result
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyResolutionState)
    (proposalPresent : Bool) (proposalId bountyId resultCount : Nat)
    (result : CallbackResult) (policy : BondPolicyAmounts)
    (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (hcount : resultCount ≠ 1) :
    runBountyCallbackExport raw ctx state proposalPresent proposalId
      bountyId resultCount result policy proposer encodeBounty
      encodeProposal encodeRoot = none := by
  simp [runBountyCallbackExport, finishBountyPayout, hcount]

private theorem bounty_key_ne_proposal_key (bountyId proposalId : Nat) :
    daoBountyEntryKey bountyId ≠ daoProposalEntryKey proposalId := by
  simp [daoBountyEntryKey, daoProposalEntryKey]

private theorem bounty_key_ne_root (bountyId : Nat) :
    daoBountyEntryKey bountyId ≠ daoRootKey := by
  intro heq
  have hlength := congrArg List.length heq
  simp [dao_bounty_key_length, daoRootKey] at hlength

private theorem proposal_key_ne_root (proposalId : Nat) :
    daoProposalEntryKey proposalId ≠ daoRootKey := by
  intro heq
  have hlength := congrArg List.length heq
  simp [dao_proposal_key_length, daoRootKey] at hlength

theorem bounty_callback_raw_bounty_effect
    (raw : BountyRawTrie) (proposalId bountyId : Nat)
    (result : CallbackResult) (outcome : BountyPayoutCallbackOutcome)
    (encodeBounty encodeProposal :
      BountyPayoutCallbackOutcome → BountyBytes) :
    (bountyCallbackRaw raw proposalId bountyId result outcome
      encodeBounty encodeProposal) (daoBountyEntryKey bountyId) =
      if result == .success then
        outcome.state.times.map (fun _ => encodeBounty outcome)
      else raw (daoBountyEntryKey bountyId) := by
  have hkey := bounty_key_ne_proposal_key bountyId proposalId
  cases result with
  | failure =>
      simp [bountyCallbackRaw, bountyRawWrite, hkey]
  | success =>
      cases ht : outcome.state.times with
      | none =>
          simp [bountyCallbackRaw, ht, bountyRawWrite,
            bountyRawRemove, hkey]
      | some times =>
          simp [bountyCallbackRaw, ht, bountyRawWrite, hkey]

theorem bounty_callback_export_success_body
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyResolutionState) (proposalPresent : Bool)
    (proposalId bountyId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (outcome : BountyPayoutCallbackOutcome)
    (h : runBountyCallbackExport raw ctx (some state) proposalPresent
      proposalId bountyId resultCount result policy proposer encodeBounty
      encodeProposal encodeRoot = some (final, outcome)) :
    finishBountyPayout state proposalPresent
      (ctx.current == ctx.predecessor) resultCount result policy proposer =
      some outcome := by
  by_cases hproposal : proposalId < 256 ^ 8
  · by_cases hbounty : bountyId < 256 ^ 8
    · cases hf : finishBountyPayout state proposalPresent
          (ctx.current == ctx.predecessor) resultCount result policy proposer with
      | none => simp [runBountyCallbackExport, hf] at h
      | some computed =>
          cases hw : runGeneratedCallWrapper raw "on_proposal_callback"
              { ctx with stateDecoded := true }
              (some (bountyCallbackRaw raw proposalId bountyId result
                computed encodeBounty encodeProposal,
                encodeRoot computed)) with
          | none =>
              simp [runBountyCallbackExport, hf, hw] at h
          | some produced =>
              simp [runBountyCallbackExport, hproposal, hbounty,
                hf, hw] at h
              exact congrArg some h.2
    · simp [runBountyCallbackExport, hbounty] at h
  · simp [runBountyCallbackExport, hproposal] at h

theorem bounty_callback_export_success_keys
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyResolutionState) (proposalPresent : Bool)
    (proposalId bountyId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (outcome : BountyPayoutCallbackOutcome)
    (h : runBountyCallbackExport raw ctx (some state) proposalPresent
      proposalId bountyId resultCount result policy proposer encodeBounty
      encodeProposal encodeRoot = some (final, outcome)) :
    final (daoProposalEntryKey proposalId) =
      some (encodeProposal outcome) ∧
    final daoRootKey = some (encodeRoot outcome) ∧
    final (daoBountyEntryKey bountyId) =
      (if result == .success then
        outcome.state.times.map (fun _ => encodeBounty outcome)
      else raw (daoBountyEntryKey bountyId)) := by
  have hbody := bounty_callback_export_success_body raw final ctx state
    proposalPresent proposalId bountyId resultCount result policy
    proposer encodeBounty encodeProposal encodeRoot outcome h
  by_cases hproposal : proposalId < 256 ^ 8
  · by_cases hbounty : bountyId < 256 ^ 8
    · have hw : runGeneratedCallWrapper raw "on_proposal_callback"
          { ctx with stateDecoded := true }
          (some (bountyCallbackRaw raw proposalId bountyId result
            outcome encodeBounty encodeProposal, encodeRoot outcome)) =
          some final := by
        cases hwopt : runGeneratedCallWrapper raw
            "on_proposal_callback" { ctx with stateDecoded := true }
            (some (bountyCallbackRaw raw proposalId bountyId result
              outcome encodeBounty encodeProposal, encodeRoot outcome)) with
        | none =>
            simp [runBountyCallbackExport, hbody, hwopt] at h
        | some produced =>
            simp [runBountyCallbackExport, hproposal, hbounty,
              hbody, hwopt] at h
            subst produced
            rfl
      have hfinal := generated_call_success_is_root_write raw
        (bountyCallbackRaw raw proposalId bountyId result outcome
          encodeBounty encodeProposal) final "on_proposal_callback"
        { ctx with stateDecoded := true } (encodeRoot outcome) hw
      rw [hfinal]
      have hproposalRoot := proposal_key_ne_root proposalId
      have hbountyRoot := bounty_key_ne_root bountyId
      refine ⟨?_, ?_, ?_⟩
      · simp [bountyRawWrite, bountyCallbackRaw, hproposalRoot]
      · simp [bountyRawWrite]
      · simp [bountyRawWrite, hbountyRoot,
          bounty_callback_raw_bounty_effect]
    · simp [runBountyCallbackExport, hbounty] at h
  · simp [runBountyCallbackExport, hproposal] at h

private theorem successful_bounty_callback_times
    (state : BountyResolutionState) (present self : Bool)
    (count previous : Nat) (policy : BondPolicyAmounts)
    (proposer : String) (outcome : BountyPayoutCallbackOutcome)
    (htimes : state.times = some previous)
    (h : finishBountyPayout state present self count .success
      policy proposer = some outcome) :
    outcome.state.times =
      if previous == 0 then none else some (previous - 1) := by
  simp [finishBountyPayout, successfulPayoutCallback,
    htimes] at h
  cases h.2
  simp

theorem bounty_callback_one_stores_zero_times
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyResolutionState) (proposalPresent : Bool)
    (proposalId bountyId resultCount : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (outcome : BountyPayoutCallbackOutcome)
    (htimes : state.times = some 1)
    (h : runBountyCallbackExport raw ctx (some state) proposalPresent
      proposalId bountyId resultCount .success policy proposer
      encodeBounty encodeProposal encodeRoot = some (final, outcome)) :
    outcome.state.times = some 0 ∧
      final (daoBountyEntryKey bountyId) = some (encodeBounty outcome) := by
  have hbody := bounty_callback_export_success_body raw final ctx state
    proposalPresent proposalId bountyId resultCount .success policy
    proposer encodeBounty encodeProposal encodeRoot outcome h
  have hnext := successful_bounty_callback_times state proposalPresent
    (ctx.current == ctx.predecessor) resultCount 1 policy proposer
    outcome htimes hbody
  have hkeys := (bounty_callback_export_success_keys raw final ctx state
    proposalPresent proposalId bountyId resultCount .success policy
    proposer encodeBounty encodeProposal encodeRoot outcome h).2.2
  simp at hnext
  simp [hnext] at hkeys
  exact ⟨hnext, hkeys⟩

theorem bounty_callback_zero_removes_bounty_key
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyResolutionState) (proposalPresent : Bool)
    (proposalId bountyId resultCount : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (outcome : BountyPayoutCallbackOutcome)
    (htimes : state.times = some 0)
    (h : runBountyCallbackExport raw ctx (some state) proposalPresent
      proposalId bountyId resultCount .success policy proposer
      encodeBounty encodeProposal encodeRoot = some (final, outcome)) :
    outcome.state.times = none ∧
      final (daoBountyEntryKey bountyId) = none := by
  have hbody := bounty_callback_export_success_body raw final ctx state
    proposalPresent proposalId bountyId resultCount .success policy
    proposer encodeBounty encodeProposal encodeRoot outcome h
  have hnext := successful_bounty_callback_times state proposalPresent
    (ctx.current == ctx.predecessor) resultCount 0 policy proposer
    outcome htimes hbody
  have hkeys := (bounty_callback_export_success_keys raw final ctx state
    proposalPresent proposalId bountyId resultCount .success policy
    proposer encodeBounty encodeProposal encodeRoot outcome h).2.2
  simp at hnext
  simp [hnext] at hkeys
  exact ⟨hnext, hkeys⟩

theorem failed_bounty_callback_preserves_bounty_key
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyResolutionState) (proposalPresent : Bool)
    (proposalId bountyId resultCount : Nat)
    (policy : BondPolicyAmounts) (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes)
    (outcome : BountyPayoutCallbackOutcome)
    (h : runBountyCallbackExport raw ctx (some state) proposalPresent
      proposalId bountyId resultCount .failure policy proposer
      encodeBounty encodeProposal encodeRoot = some (final, outcome)) :
    final (daoBountyEntryKey bountyId) = raw (daoBountyEntryKey bountyId) := by
  have hkeys := (bounty_callback_export_success_keys raw final ctx state
    proposalPresent proposalId bountyId resultCount .failure policy
    proposer encodeBounty encodeProposal encodeRoot outcome h).2.2
  simpa using hkeys

end SputnikDAO2
