import Model.FactoryGovernanceExport
import Proofs.FactoryViewRefinement
import Proofs.BlobKeySeparation

namespace SputnikDAO2

theorem approved_factory_update_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (info : FactoryInfo)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0) :
    runApprovedFactoryInfoUpdateExport raw wrapper true true id info
      proposalBytes rootBytes =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoFactoryKey (encodeFactoryInfo info))
          (daoProposalEntryKey id) proposalBytes)
        daoRootKey rootBytes) := by
  have hi : findDAOExport "act_proposal" =
      some ⟨"act_proposal", .call, false, false⟩ := by decide
  simp [runApprovedFactoryInfoUpdateExport, Nat.not_lt.mpr hid,
    hproposal, runGeneratedCallWrapper, hi, hargs, hdeposit]

theorem approved_factory_update_stores_factory_bytes
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (info : FactoryInfo)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedFactoryInfoUpdateExport raw wrapper true true
      id info proposalBytes rootBytes = some final) :
    final daoFactoryKey = some (encodeFactoryInfo info) := by
  rw [approved_factory_update_three_key_image raw wrapper id info
    proposalBytes rootBytes oldProposal hid hproposal hargs hdeposit] at hrun
  cases hrun
  have hfactoryRoot : daoFactoryKey ≠ daoRootKey := by decide
  have hfactoryProposal : daoFactoryKey ≠ daoProposalEntryKey id := by
    intro heq
    have hlength := congrArg List.length heq
    simp [dao_proposal_key_length, daoFactoryKey] at hlength
  simp [bountyRawWrite, hfactoryRoot, hfactoryProposal]

theorem approved_factory_update_nonpayable
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (stateDecoded approvedBody : Bool) (id : Nat)
    (info : FactoryInfo) (proposalBytes rootBytes : BountyBytes)
    (hdeposit : wrapper.attachedDeposit ≠ 0) :
    runApprovedFactoryInfoUpdateExport raw wrapper stateDecoded
      approvedBody id info proposalBytes rootBytes = none := by
  have hi : findDAOExport "act_proposal" =
      some ⟨"act_proposal", .call, false, false⟩ := by decide
  simp [runApprovedFactoryInfoUpdateExport, runGeneratedCallWrapper,
    hi, hdeposit]

theorem approved_factory_update_next_view_reads_info
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (info : FactoryInfo)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (deposit : Nat) (current : String)
    (validAccount : String → Bool)
    (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedFactoryInfoUpdateExport raw wrapper true true
      id info proposalBytes rootBytes = some final)
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true) :
    runParsedFactoryInfoView final (some ()) deposit current
      validAccount = some (info, final) := by
  have hraw := approved_factory_update_stores_factory_bytes raw final
    wrapper id info proposalBytes rootBytes oldProposal hid hproposal
    hargs hdeposit hrun
  exact parsed_factory_view_stored_bytes final deposit current
    validAccount info hraw hfits hvalid

theorem approved_factory_disable_blocks_next_external_update
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (factory : String)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (ctx : RawUpdateContext) (validAccount : String → Bool)
    (hashCode : CodeBytes → String)
    (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedFactoryInfoUpdateExport raw wrapper true true
      id ⟨factory, false⟩ proposalBytes rootBytes = some final)
    (hfits : wireStringFits factory)
    (hvalid : validAccount factory = true)
    (hcaller : ctx.predecessor = factory)
    (hnotself : ctx.predecessor ≠ ctx.current) :
    runParsedUpdateExport final ctx validAccount hashCode = none := by
  have hraw := approved_factory_update_stores_factory_bytes raw final
    wrapper id ⟨factory, false⟩ proposalBytes rootBytes oldProposal
    hid hproposal hargs hdeposit hrun
  exact parsed_update_disabled_factory_denies_external_caller final ctx
    validAccount hashCode factory hraw hfits hvalid hcaller hnotself

end SputnikDAO2
