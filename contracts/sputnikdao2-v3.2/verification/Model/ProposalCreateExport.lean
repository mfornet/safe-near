import Model.ExportWrapper
import Model.ProposalCreate
import Model.BlobKeySeparation

namespace SputnikDAO2

/-! `add_proposal` export projection. Wrapper caller and attached deposit are
authoritative for the body context. The policy, block metadata, argument
decoding and full Contract/proposal serializers are separate inputs.
Legacy `LookupMap.insert` deserializes an occupied old value even when the
caller ignores it, so `oldProposalDecoded` guards occupied raw keys. -/

def runAddProposalExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option ProposalCreateState)
    (create : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes) :
    Option (BountyRawTrie × Nat) := do
  let before ← state
  let bodyCtx : ProposalCreateContext :=
    ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
      wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
  let (after, id) ← addProposal before bodyCtx kind description
  let proposal ← proposalAt after.proposals id
  if (raw (daoProposalEntryKey id)).isSome && !oldProposalDecoded then
    none else pure ()
  let afterRaw := bountyRawWrite raw (daoProposalEntryKey id)
    (encodeProposal proposal)
  let final ← runGeneratedCallWrapper raw "add_proposal"
    { wrapper with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot after))
  some (final, id)

end SputnikDAO2
