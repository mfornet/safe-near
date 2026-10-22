import Model.ExportWrapper
import Model.Finalize
import Model.BlobKeySeparation
import Model.ProposalCreate

namespace SputnikDAO2

structure VoteFinalizeLog where
  account : String
  proposalId : Nat
  blockHeight : Nat
  deriving Repr, DecidableEq

structure VoteFinalizeState where
  proposalPresent : Bool
  status : ProposalStatus
  proposer : String
  locked : Nat
  globalLog : List VoteFinalizeLog
  deriving Repr, DecidableEq

structure VoteFinalizeResult where
  status : ProposalStatus
  locked : Nat
  globalLog : List VoteFinalizeLog
  detachedRefund : BondTransfer
  effect : FinalizeEffect
  deriving Repr, DecidableEq

/-! Finalize for `ProposalKind::Vote`: either Approved executes the synchronous
Vote action or Expired rejects it. Both schedule the CURRENT proposal bond
refund and insert the updated proposal. Other kinds may write additional raw
keys or schedule callbacks and are outside this projection. -/
def runVoteFinalize (state : VoteFinalizeState) (ctx : FinalizeContext)
    (account : String) (proposalId blockHeight : Nat)
    (policy : BondPolicyAmounts) : Option VoteFinalizeResult := do
  let plan ← selectFinalize { ctx with
    proposalExists := state.proposalPresent,
    originalStatus := state.status }
  let bonds := returnProposalBonds state.locked policy state.proposer false
  some ⟨plan.storedStatus, bonds.lockedAfter,
    appendLog20 state.globalLog ⟨account, proposalId, blockHeight⟩,
    bonds.returnedTransfer, plan.effect⟩

def runVoteFinalizeExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option VoteFinalizeState)
    (ctx : FinalizeContext) (id blockHeight : Nat)
    (policyReadable storedKindIsVote storedDecoded : Bool)
    (bondPolicy : BondPolicyAmounts)
    (encodeProposal : VoteFinalizeResult → BountyBytes)
    (encodeRoot : VoteFinalizeResult → BountyBytes) :
    Option (BountyRawTrie × VoteFinalizeResult) := do
  let before ← state
  if id > maxU64 || blockHeight > maxU64 ||
      ctx.submission > maxU64 || ctx.period > maxU64 ||
      ctx.now > maxU64 || ctx.submission + ctx.period > maxU64 ||
      ctx.totalSupply > maxU128 || before.locked > maxU128 ||
      bondPolicy.proposalBond > maxU128 ||
      !policyReadable || !storedKindIsVote || !storedDecoded then none else
  let _ ← raw (daoProposalEntryKey id)
  let result ← runVoteFinalize before ctx wrapper.predecessor id
    blockHeight bondPolicy
  let afterRaw := bountyRawWrite raw (daoProposalEntryKey id)
    (encodeProposal result)
  let final ← runGeneratedCallWrapper raw "act_proposal"
    { wrapper with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot result))
  some (final, result)

end SputnikDAO2
