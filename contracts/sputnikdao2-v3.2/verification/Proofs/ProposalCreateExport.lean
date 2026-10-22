import Model.ProposalCreateExport
import Proofs.ExportWrapper
import Proofs.ProposalCreate
import Proofs.BlobKeySeparation

namespace SputnikDAO2

private theorem add_proposal_result_id
    (state next : ProposalCreateState) (ctx : ProposalCreateContext)
    (kind : ProposalKindCheck) (description : String) (id : Nat)
    (h : addProposal state ctx kind description = some (next, id)) :
    id = state.lastId := by
  by_cases hbond : ctx.attached = ctx.policyBond
  · by_cases hkind : validAddKind state.stakingSet kind = true
    · by_cases hpermission : ctx.addPermission = true
      · by_cases hroom : state.lastId < maxU64
        · simp [addProposal, hbond, hkind, hpermission,
            Nat.not_le.mpr hroom] at h
          exact h.2.symm
        · simp [addProposal, hbond, hkind, hpermission,
            Nat.le_of_not_gt hroom] at h
      · simp [addProposal, hbond, hkind, hpermission] at h
    · simp [addProposal, hbond, hkind] at h
  · simp [addProposal, hbond] at h

theorem add_proposal_export_wrong_bond_aborts
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : Option ProposalCreateState)
    (create : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes)
    (hbond : wrapper.attachedDeposit ≠ create.policyBond) :
    runAddProposalExport raw wrapper state create kind description
      oldProposalDecoded encodeProposal encodeRoot = none := by
  cases state with
  | none => simp [runAddProposalExport]
  | some before =>
      simp [runAddProposalExport, addProposal, hbond]

theorem add_proposal_export_rejects_malformed_old_value
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : ProposalCreateState)
    (create : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes)
    (hoccupied : (raw (daoProposalEntryKey state.lastId)).isSome = true) :
    runAddProposalExport raw wrapper (some state) create kind
      description false encodeProposal encodeRoot = none := by
  let bodyCtx : ProposalCreateContext :=
    ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
      wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
  cases ha : addProposal state bodyCtx kind description with
  | none => simp [runAddProposalExport, bodyCtx, ha]
  | some pair =>
      obtain ⟨after, id⟩ := pair
      have hid := add_proposal_result_id state after bodyCtx kind
        description id ha
      subst id
      cases hp : proposalAt after.proposals state.lastId with
      | none => simp [runAddProposalExport, bodyCtx, ha, hp]
      | some proposal =>
          simp [runAddProposalExport, bodyCtx, ha, hp, hoccupied]

theorem add_proposal_export_success_keys
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : ProposalCreateState) (create : ProposalCreateContext)
    (kind : ProposalKindCheck) (description : String)
    (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes)
    (id : Nat)
    (h : runAddProposalExport raw wrapper (some state) create kind
      description oldProposalDecoded encodeProposal encodeRoot =
      some (final, id)) :
    ∃ after proposal,
      id = state.lastId ∧
      addProposal state
        ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
          wrapper.attachedDeposit, create.policyBond,
          create.addPermission⟩ kind description = some (after, id) ∧
      proposalAt after.proposals id = some proposal ∧
      final (daoProposalEntryKey id) = some (encodeProposal proposal) ∧
      final daoRootKey = some (encodeRoot after) := by
  let bodyCtx : ProposalCreateContext :=
    ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
      wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
  cases ha : addProposal state bodyCtx kind description with
  | none => simp [runAddProposalExport, bodyCtx, ha] at h
  | some pair =>
      obtain ⟨after, actualId⟩ := pair
      cases hp : proposalAt after.proposals actualId with
      | none => simp [runAddProposalExport, bodyCtx, ha, hp] at h
      | some proposal =>
          by_cases hdecode :
              (raw (daoProposalEntryKey actualId)).isSome &&
                !oldProposalDecoded = true
          · cases oldProposalDecoded with
            | false =>
                simp at hdecode
                simp [runAddProposalExport, bodyCtx, ha, hp,
                  hdecode] at h
            | true => simp at hdecode
          · cases hw : runGeneratedCallWrapper raw "add_proposal"
                { wrapper with stateDecoded := true }
                (some (bountyRawWrite raw (daoProposalEntryKey actualId)
                  (encodeProposal proposal), encodeRoot after)) with
            | none =>
                simp [runAddProposalExport, bodyCtx, ha, hp,
                  hw] at h
            | some produced =>
                simp [runAddProposalExport, bodyCtx, ha, hp,
                  hw] at h
                rcases h with ⟨_, ⟨hfinal, hid⟩⟩
                subst final
                subst id
                have hactual := add_proposal_result_id state after bodyCtx
                  kind description actualId ha
                have hroot := generated_call_success_is_root_write raw
                  (bountyRawWrite raw (daoProposalEntryKey actualId)
                    (encodeProposal proposal)) produced "add_proposal"
                  { wrapper with stateDecoded := true }
                  (encodeRoot after) hw
                have hkey : daoProposalEntryKey actualId ≠ daoRootKey := by
                  intro heq
                  have hlength := congrArg List.length heq
                  simp [dao_proposal_key_length, daoRootKey] at hlength
                refine ⟨after, proposal, hactual, rfl, hp, ?_, ?_⟩
                · rw [hroot]
                  simp [bountyRawWrite, hkey]
                · rw [hroot]
                  simp [bountyRawWrite]

end SputnikDAO2
