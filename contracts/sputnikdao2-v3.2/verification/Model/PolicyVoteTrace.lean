import Model.PolicyGovernanceExport
import Model.FactoryVoteTrace

namespace SputnikDAO2

/-! Approved ChangePolicy voting path. The old policy must decode as Current
from raw key 1 before permission/vote evaluation; this binding is checked by
the underlying export. A Default replacement can arise only from an existing
synthetic proposal because public creation rejects it. -/
def runPolicyApprovalVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option FactoryVoteState)
    (id : Nat) (newPolicy : WireVersionedPolicy) (choice : VoteChoice)
    (blockHeight userWeight submission period now totalSupply : Nat)
    (oldBondPolicy : BondPolicyAmounts)
    (permissionAllowed exactKindMatches : Bool)
    (encodeProposal : FactoryVoteResult → BountyBytes)
    (encodeRoot : FactoryVoteResult → BountyBytes) :
    Option (BountyRawTrie × FactoryVoteResult) := do
  let before ← state
  if id > maxU64 || blockHeight > maxU64 ||
      !permissionAllowed || !exactKindMatches then none else pure ()
  let result ← runFactoryApprovalVote before wrapper.predecessor id choice
    blockHeight userWeight submission period now totalSupply oldBondPolicy
  let final ← runApprovedChangePolicyExport raw wrapper
    state.isSome true id newPolicy
    (encodeProposal result) (encodeRoot result)
  some (final, result)

end SputnikDAO2
