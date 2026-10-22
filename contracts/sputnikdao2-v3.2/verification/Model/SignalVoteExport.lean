import Model.ExportWrapper
import Model.VoteSignal
import Model.BlobKeySeparation

namespace SputnikDAO2

/-! Export projection for `act_proposal` when the stored proposal kind is
`Vote` and the action is one of the three voting actions. The loaded policy,
kind equality, role selection, vote rules, host metadata and serializers are
explicit inputs. `storedDecoded` models the initial LookupMap read; a
successful read of the same key also suffices for the final insertion's old
value decode. -/
def signalVoteRawEffect (raw : BountyRawTrie) (id : Nat)
    (result : SignalVoteResult)
    (encodeProposal : SignalVoteResult → BountyBytes) : BountyRawTrie :=
  match result.effect with
  | .deleteProposal => bountyRawRemove raw (daoProposalEntryKey id)
  | .storeOnly | .refundBond =>
      bountyRawWrite raw (daoProposalEntryKey id) (encodeProposal result)

def runSignalVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option SignalVoteState)
    (ctx : SignalVoteContext) (id : Nat)
    (policyReadable storedKindIsVote storedDecoded : Bool)
    (encodeProposal : SignalVoteResult → BountyBytes)
    (encodeRoot : SignalVoteResult → BountyBytes) :
    Option (BountyRawTrie × SignalVoteResult) := do
  let before ← state
  if id > maxU64 || !policyReadable || !storedKindIsVote ||
      !storedDecoded then none else
  let _ ← raw (daoProposalEntryKey id)
  let bodyCtx : SignalVoteContext :=
    { ctx with account := wrapper.predecessor, proposalId := id }
  let result ← runSignalVote before bodyCtx
  let afterRaw := signalVoteRawEffect raw id result encodeProposal
  let final ← runGeneratedCallWrapper raw "act_proposal"
    { wrapper with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot result))
  some (final, result)

end SputnikDAO2
