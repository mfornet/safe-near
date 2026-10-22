import Model.FactoryFinalizeTrace
import Proofs.FactoryGovernanceExport
import Proofs.Finalize

namespace SputnikDAO2

theorem factory_approved_finalize_effects
    (state : FactoryFinalizeState) (ctx : FinalizeContext)
    (account : String) (id height : Nat)
    (policy : BondPolicyAmounts)
    (hselect : selectFinalize { ctx with
      proposalExists := state.proposalPresent,
      originalStatus := state.status } =
      some ⟨.approved, .executeProposal⟩) :
    runFactoryApprovedFinalize state ctx account id height policy =
      some ⟨.approved, state.locked - policy.proposalBond,
        appendLog20 state.globalLog ⟨account, id, height⟩,
        ⟨state.proposer, policy.proposalBond⟩⟩ := by
  simp [runFactoryApprovedFinalize, hselect, returnProposalBonds]

theorem factory_finalize_zero_lock_still_schedules_bond
    (present : Bool) (status : ProposalStatus) (proposer : String)
    (log : List VoteFinalizeLog) (ctx : FinalizeContext)
    (account : String) (id height : Nat)
    (policy : BondPolicyAmounts)
    (hselect : selectFinalize { ctx with
      proposalExists := present, originalStatus := status } =
      some ⟨.approved, .executeProposal⟩) :
    runFactoryApprovedFinalize
      ⟨present, status, proposer, 0, log⟩ ctx account id height policy =
      some ⟨.approved, 0,
        appendLog20 log ⟨account, id, height⟩,
        ⟨proposer, policy.proposalBond⟩⟩ := by
  simpa using factory_approved_finalize_effects
    ⟨present, status, proposer, 0, log⟩ ctx account id height policy
    hselect

theorem factory_approved_finalize_export_three_key_image
    (raw : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : FactoryFinalizeState) (ctx : FinalizeContext)
    (id height : Nat) (info : FactoryInfo)
    (policy : BondPolicyAmounts)
    (encodeProposal encodeRoot : FactoryFinalizeResult → BountyBytes)
    (result : FactoryFinalizeResult) (oldProposal : BountyBytes)
    (hid : id ≤ maxU64) (hheight : height ≤ maxU64)
    (hsubmission : ctx.submission ≤ maxU64)
    (hperiod : ctx.period ≤ maxU64)
    (hnow : ctx.now ≤ maxU64)
    (hdeadline : ctx.submission + ctx.period ≤ maxU64)
    (hsupply : ctx.totalSupply ≤ maxU128)
    (hlocked : state.locked ≤ maxU128)
    (hbond : policy.proposalBond ≤ maxU128)
    (hstep : runFactoryApprovedFinalize state ctx wrapper.predecessor
      id height policy = some result)
    (hproposal : raw (daoProposalEntryKey id) = some oldProposal)
    (hargs : wrapper.argumentsDecoded = true)
    (hdeposit : wrapper.attachedDeposit = 0) :
    runFactoryApprovedFinalizeExport raw wrapper (some state) ctx id height
      info true true policy encodeProposal encodeRoot =
      some (bountyRawWrite
        (bountyRawWrite
          (bountyRawWrite raw daoFactoryKey (encodeFactoryInfo info))
          (daoProposalEntryKey id) (encodeProposal result))
        daoRootKey (encodeRoot result), result) := by
  have hwrite := approved_factory_update_three_key_image raw wrapper id info
    (encodeProposal result) (encodeRoot result) oldProposal
    hid hproposal hargs hdeposit
  simp [runFactoryApprovedFinalizeExport, Nat.not_lt.mpr hid,
    Nat.not_lt.mpr hheight, Nat.not_lt.mpr hsubmission,
    Nat.not_lt.mpr hperiod, Nat.not_lt.mpr hnow,
    Nat.not_lt.mpr hdeadline, Nat.not_lt.mpr hsupply,
    Nat.not_lt.mpr hlocked, Nat.not_lt.mpr hbond,
    hstep, hwrite]

end SputnikDAO2
