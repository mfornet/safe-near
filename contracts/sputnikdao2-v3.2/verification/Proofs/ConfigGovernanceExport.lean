import Model.ConfigGovernanceExport
import Proofs.ConfigPolicyDecoding
import Proofs.BlobKeySeparation

namespace SputnikDAO2

theorem approved_config_update_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (config : WireConfig)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0) :
    runApprovedChangeConfigExport raw wrapper true true id config
      proposalBytes rootBytes =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoConfigKey (encodeWireConfig config))
          (daoProposalEntryKey id) proposalBytes)
        daoRootKey rootBytes) := by
  have hi : findDAOExport "act_proposal" =
      some ⟨"act_proposal", .call, false, false⟩ := by decide
  simp [runApprovedChangeConfigExport, Nat.not_lt.mpr hid,
    hproposal, runGeneratedCallWrapper, hi, hargs, hdeposit]

theorem approved_config_update_stores_config_bytes
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (config : WireConfig)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedChangeConfigExport raw wrapper true true id config
      proposalBytes rootBytes = some final) :
    final daoConfigKey = some (encodeWireConfig config) := by
  rw [approved_config_update_three_key_image raw wrapper id config
    proposalBytes rootBytes oldProposal hid hproposal hargs hdeposit] at hrun
  cases hrun
  have hconfigRoot : daoConfigKey ≠ daoRootKey := by decide
  have hconfigProposal : daoConfigKey ≠ daoProposalEntryKey id := by
    intro heq
    have hlength := congrArg List.length heq
    simp [dao_proposal_key_length, daoConfigKey] at hlength
  simp [bountyRawWrite, hconfigRoot, hconfigProposal]

theorem parsed_config_view_reads_stored_bytes
    (raw : BountyRawTrie) (deposit : Nat) (config : WireConfig)
    (hraw : raw daoConfigKey = some (encodeWireConfig config))
    (hfits : wireConfigFits config) :
    runParsedConfigView raw (some ()) deposit = some (config, raw) := by
  have hi : findDAOExport "get_config" =
      some ⟨"get_config", .view, false, false⟩ := by decide
  simp [runParsedConfigView, hraw,
    parse_wire_config_exact_encoded config hfits,
    runGeneratedViewWrapper, hi, runViewWrapper]

theorem parsed_config_view_requires_root_decode
    (raw : BountyRawTrie) (deposit : Nat) :
    runParsedConfigView raw none deposit = none := by
  simp [runParsedConfigView]

theorem parsed_config_view_missing_key_aborts
    (raw : BountyRawTrie) (deposit : Nat)
    (hraw : raw daoConfigKey = none) :
    runParsedConfigView raw (some ()) deposit = none := by
  simp [runParsedConfigView, hraw]

theorem parsed_config_view_trailing_byte_aborts
    (raw : BountyRawTrie) (deposit : Nat) (config : WireConfig)
    (extra : UInt8)
    (hraw : raw daoConfigKey =
      some (encodeWireConfig config ++ [extra]))
    (hfits : wireConfigFits config) :
    runParsedConfigView raw (some ()) deposit = none := by
  simp [runParsedConfigView, hraw,
    parse_wire_config_rejects_trailing_byte config extra hfits]

theorem approved_config_update_next_view_reads_config
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (config : WireConfig)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (deposit : Nat) (hid : id ≤ maxU64)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedChangeConfigExport raw wrapper true true id config
      proposalBytes rootBytes = some final)
    (hfits : wireConfigFits config) :
    runParsedConfigView final (some ()) deposit = some (config, final) := by
  have hraw := approved_config_update_stores_config_bytes raw final
    wrapper id config proposalBytes rootBytes oldProposal
    hid hproposal hargs hdeposit hrun
  exact parsed_config_view_reads_stored_bytes final deposit config hraw hfits

end SputnikDAO2
