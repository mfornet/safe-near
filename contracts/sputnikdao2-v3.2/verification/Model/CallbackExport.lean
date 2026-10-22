import Model.ExportWrapper
import Model.TransferExecution
import Model.BlobKeySeparation

namespace SputnikDAO2

/-! Non-BountyDone callback composition. The result is the transfer/function
call callback projection; bounty-specific storage effects and exact complete
Contract/proposal serialization remain separate. `result` represents the one
runtime promise result after SDK decoding. -/

def runOrdinaryCallbackExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option TransferCallbackState)
    (proposalId resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts)
    (encodeProposal : TransferCallbackResult → BountyBytes)
    (encodeRoot : TransferCallbackResult → BountyBytes) :
    Option (BountyRawTrie × TransferCallbackResult) := do
  if proposalId ≥ 256 ^ 8 then none else pure ()
  let before ← state
  let after ← finishTransferCallback before
    (ctx.current == ctx.predecessor) resultCount result policy
  let afterRaw := bountyRawWrite raw
    (daoProposalEntryKey proposalId) (encodeProposal after)
  let final ← runGeneratedCallWrapper raw "on_proposal_callback"
    { ctx with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot after))
  some (final, after)

end SputnikDAO2
