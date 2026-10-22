import Model.FactoryGovernanceExport
import Model.Finalize
import Model.VoteFinalizeExport

namespace SputnikDAO2

structure FactoryFinalizeState where
  proposalPresent : Bool
  status : ProposalStatus
  proposer : String
  locked : Nat
  globalLog : List VoteFinalizeLog
  deriving Repr, DecidableEq

structure FactoryFinalizeResult where
  status : ProposalStatus
  locked : Nat
  globalLog : List VoteFinalizeLog
  detachedRefund : BondTransfer
  deriving Repr, DecidableEq

/-! `Finalize` may re-execute a FactoryInfoUpdate when status recomputation
selects Approved. It schedules the current proposal bond again; no guard here
asserts that an earlier execution has not already refunded it. -/
def runFactoryApprovedFinalize (state : FactoryFinalizeState)
    (ctx : FinalizeContext) (account : String) (id height : Nat)
    (policy : BondPolicyAmounts) : Option FactoryFinalizeResult := do
  let plan ← selectFinalize { ctx with
    proposalExists := state.proposalPresent,
    originalStatus := state.status }
  if plan.effect != .executeProposal then none else
  let bonds := returnProposalBonds state.locked policy state.proposer false
  some ⟨plan.storedStatus, bonds.lockedAfter,
    appendLog20 state.globalLog ⟨account, id, height⟩,
    bonds.returnedTransfer⟩

def runFactoryApprovedFinalizeExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option FactoryFinalizeState)
    (ctx : FinalizeContext) (id height : Nat) (info : FactoryInfo)
    (policyReadable storedKindMatches : Bool)
    (policy : BondPolicyAmounts)
    (encodeProposal : FactoryFinalizeResult → BountyBytes)
    (encodeRoot : FactoryFinalizeResult → BountyBytes) :
    Option (BountyRawTrie × FactoryFinalizeResult) := do
  let before ← state
  if id > maxU64 || height > maxU64 ||
      ctx.submission > maxU64 || ctx.period > maxU64 ||
      ctx.now > maxU64 || ctx.submission + ctx.period > maxU64 ||
      ctx.totalSupply > maxU128 || before.locked > maxU128 ||
      policy.proposalBond > maxU128 ||
      !policyReadable || !storedKindMatches then none else pure ()
  let result ← runFactoryApprovedFinalize before ctx
    wrapper.predecessor id height policy
  let final ← runApprovedFactoryInfoUpdateExport raw wrapper
    state.isSome true id info (encodeProposal result) (encodeRoot result)
  some (final, result)

end SputnikDAO2
