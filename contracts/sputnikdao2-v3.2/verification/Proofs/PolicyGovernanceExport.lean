import Model.PolicyGovernanceExport
import Proofs.ConfigPolicyDecoding
import Proofs.BlobKeySeparation

namespace SputnikDAO2

theorem encoded_current_policy_is_readable
    (raw : BountyRawTrie) (policy : WirePolicy)
    (hraw : raw daoPolicyKey =
      some (encodeWireVersionedPolicy (.current policy)))
    (hfits : wireVersionedPolicyFits (.current policy)) :
    policyReadableFromRaw raw = true := by
  simp [policyReadableFromRaw, hraw,
    parse_wire_policy_exact_encoded (.current policy) hfits]

theorem encoded_legacy_policy_is_unreadable
    (raw : BountyRawTrie) (council : List String)
    (hraw : raw daoPolicyKey =
      some (encodeWireVersionedPolicy (.default council)))
    (hfits : wireVersionedPolicyFits (.default council)) :
    policyReadableFromRaw raw = false := by
  simp [policyReadableFromRaw, hraw,
    parse_wire_policy_exact_encoded (.default council) hfits]

theorem missing_policy_is_unreadable
    (raw : BountyRawTrie) (hraw : raw daoPolicyKey = none) :
    policyReadableFromRaw raw = false := by
  simp [policyReadableFromRaw, hraw]

theorem unreadable_old_policy_blocks_change
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (stateDecoded approvedBody : Bool) (id : Nat)
    (policy : WireVersionedPolicy)
    (proposalBytes rootBytes : BountyBytes)
    (hread : policyReadableFromRaw raw = false) :
    runApprovedChangePolicyExport raw wrapper stateDecoded approvedBody
      id policy proposalBytes rootBytes = none := by
  simp [runApprovedChangePolicyExport, hread]

theorem approved_policy_update_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (policy : WireVersionedPolicy)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0) :
    runApprovedChangePolicyExport raw wrapper true true id policy
      proposalBytes rootBytes =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoPolicyKey
            (encodeWireVersionedPolicy policy))
          (daoProposalEntryKey id) proposalBytes)
        daoRootKey rootBytes) := by
  have hi : findDAOExport "act_proposal" =
      some ⟨"act_proposal", .call, false, false⟩ := by decide
  simp [runApprovedChangePolicyExport, Nat.not_lt.mpr hid,
    hread, hproposal, runGeneratedCallWrapper, hi, hargs, hdeposit]

theorem approved_policy_update_stores_policy_bytes
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (policy : WireVersionedPolicy)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (hid : id ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedChangePolicyExport raw wrapper true true id policy
      proposalBytes rootBytes = some final) :
    final daoPolicyKey = some (encodeWireVersionedPolicy policy) := by
  rw [approved_policy_update_three_key_image raw wrapper id policy
    proposalBytes rootBytes oldProposal hid hread hproposal hargs hdeposit] at hrun
  cases hrun
  have hpolicyRoot : daoPolicyKey ≠ daoRootKey := by decide
  have hpolicyProposal : daoPolicyKey ≠ daoProposalEntryKey id := by
    intro heq
    have hlength := congrArg List.length heq
    simp [dao_proposal_key_length, daoPolicyKey] at hlength
  simp [bountyRawWrite, hpolicyRoot, hpolicyProposal]

theorem parsed_policy_view_reads_current
    (raw : BountyRawTrie) (deposit : Nat) (policy : WirePolicy)
    (hraw : raw daoPolicyKey =
      some (encodeWireVersionedPolicy (.current policy)))
    (hfits : wireVersionedPolicyFits (.current policy)) :
    runParsedPolicyView raw (some ()) deposit = some (policy, raw) := by
  have hi : findDAOExport "get_policy" =
      some ⟨"get_policy", .view, false, false⟩ := by decide
  simp [runParsedPolicyView, hraw,
    parse_wire_policy_exact_encoded (.current policy) hfits,
    runGeneratedViewWrapper, hi, runViewWrapper]

theorem parsed_policy_view_rejects_legacy
    (raw : BountyRawTrie) (deposit : Nat) (council : List String)
    (hraw : raw daoPolicyKey =
      some (encodeWireVersionedPolicy (.default council)))
    (hfits : wireVersionedPolicyFits (.default council)) :
    runParsedPolicyView raw (some ()) deposit = none := by
  simp [runParsedPolicyView, hraw,
    parse_wire_policy_exact_encoded (.default council) hfits]

theorem approved_legacy_policy_makes_next_view_abort
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (council : List String)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (deposit : Nat) (hid : id ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedChangePolicyExport raw wrapper true true id
      (.default council) proposalBytes rootBytes = some final)
    (hfits : wireVersionedPolicyFits (.default council)) :
    runParsedPolicyView final (some ()) deposit = none := by
  have hraw := approved_policy_update_stores_policy_bytes raw final
    wrapper id (.default council) proposalBytes rootBytes oldProposal
    hid hread hproposal hargs hdeposit hrun
  exact parsed_policy_view_rejects_legacy final deposit council hraw hfits

theorem approved_current_policy_next_view_reads_it
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (id : Nat) (policy : WirePolicy)
    (proposalBytes rootBytes oldProposal : BountyBytes)
    (deposit : Nat) (hid : id ≤ maxU64)
    (hread : policyReadableFromRaw raw = true)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0)
    (hrun : runApprovedChangePolicyExport raw wrapper true true id
      (.current policy) proposalBytes rootBytes = some final)
    (hfits : wireVersionedPolicyFits (.current policy)) :
    runParsedPolicyView final (some ()) deposit = some (policy, final) := by
  have hraw := approved_policy_update_stores_policy_bytes raw final
    wrapper id (.current policy) proposalBytes rootBytes oldProposal
    hid hread hproposal hargs hdeposit hrun
  exact parsed_policy_view_reads_current final deposit policy hraw hfits

end SputnikDAO2
