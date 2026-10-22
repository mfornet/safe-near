import Model.PolicyGovernanceExport
import Model.ProposalCreateExport
import Model.ActProposalExport
import Model.SignalVoteExport
import Model.VoteFinalizeExport

namespace SputnikDAO2

/-! Shared policy-read barrier for exported proposal calls. The source
unwraps and converts the LazyOption policy before creation or action checks.
The raw parser proves a negative condition exactly; its positive relation to
near-sdk AccountId/hash-map decoding is still a refinement obligation. -/
def runRawPolicyAddProposalExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option ProposalCreateState)
    (create : ProposalCreateContext) (kind : ProposalKindCheck)
    (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : ProposalCreateState → BountyBytes) :
    Option (BountyRawTrie × Nat) :=
  if policyReadableFromRaw raw then
    runAddProposalExport raw wrapper state create kind description
      oldProposalDecoded encodeProposal encodeRoot
  else none

def runRawPolicyActNonVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option NonVoteState)
    (ctx : NonVoteContext) (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes) : Option BountyRawTrie :=
  runActNonVoteExport raw wrapper state ctx (policyReadableFromRaw raw)
    id action encodeRoot

def runRawPolicySignalVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option SignalVoteState)
    (ctx : SignalVoteContext) (id : Nat)
    (storedKindIsVote storedDecoded : Bool)
    (encodeProposal : SignalVoteResult → BountyBytes)
    (encodeRoot : SignalVoteResult → BountyBytes) :
    Option (BountyRawTrie × SignalVoteResult) :=
  runSignalVoteExport raw wrapper state ctx id
    (policyReadableFromRaw raw) storedKindIsVote storedDecoded
    encodeProposal encodeRoot

def runRawPolicyVoteFinalizeExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option VoteFinalizeState)
    (ctx : FinalizeContext) (id height : Nat)
    (storedKindIsVote storedDecoded : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal : VoteFinalizeResult → BountyBytes)
    (encodeRoot : VoteFinalizeResult → BountyBytes) :
    Option (BountyRawTrie × VoteFinalizeResult) :=
  runVoteFinalizeExport raw wrapper state ctx id height
    (policyReadableFromRaw raw) storedKindIsVote storedDecoded
    policy encodeProposal encodeRoot

end SputnikDAO2
