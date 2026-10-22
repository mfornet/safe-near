import Model.ConfigGovernanceExport
import Model.FactoryVoteTrace

namespace SputnikDAO2

/-! The selected-role vote transition is independent of the proposal kind
once policy role selection has been supplied. Reuse its approved ballot,
current-bond refund and log result for ChangeConfig, then write key 0,
the updated proposal and root. Role selection, serializers and host rollback
remain refinement inputs. -/
def runConfigApprovalVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option FactoryVoteState)
    (id : Nat) (config : WireConfig) (choice : VoteChoice)
    (blockHeight userWeight submission period now totalSupply : Nat)
    (policy : BondPolicyAmounts)
    (policyReadable permissionAllowed exactKindMatches : Bool)
    (encodeProposal : FactoryVoteResult → BountyBytes)
    (encodeRoot : FactoryVoteResult → BountyBytes) :
    Option (BountyRawTrie × FactoryVoteResult) := do
  let before ← state
  if id > maxU64 || blockHeight > maxU64 ||
      !policyReadable || !permissionAllowed || !exactKindMatches then none
  else pure ()
  let result ← runFactoryApprovalVote before wrapper.predecessor id choice
    blockHeight userWeight submission period now totalSupply policy
  let final ← runApprovedChangeConfigExport raw wrapper
    state.isSome true id config (encodeProposal result) (encodeRoot result)
  some (final, result)

end SputnikDAO2
