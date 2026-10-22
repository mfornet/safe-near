import Model.ExportWrapper
import Model.BountyTrie
import Model.ProposalCreate
import Model.BlobKeySeparation

namespace SputnikDAO2

structure BountyDoneExportState where
  bounty : BountyStorageState
  proposals : ProposalCreateState

inductive BountyDoneExportEffect where
  | expired
  | proposal (id : Nat)
  deriving Repr, DecidableEq

/-! The two projections share one serialized `locked_amount`; the equality
guard is required before composing them. The account vector may contain
claims for other bounty IDs. -/
def bountyDoneStored (state : BountyDoneExportState)
    (ctx : ProposalCreateContext) (target : Option String)
    (bountyId : Nat) (description : String) :
    Option (BountyDoneExportState × BountyDoneExportEffect) := do
  if state.bounty.locked != state.proposals.locked then none else
  let account := target.getD ctx.predecessor
  let claims ← state.bounty.claimers account
  let (claim, _) ← removeFirstBountyClaim claims bountyId
  if bountyId > maxU64 || claim.completed || claim.start > maxU64 || claim.deadline > maxU64 ||
      ctx.blockTimestamp > maxU64 || claim.start + claim.deadline > maxU64 then
    none
  else if ctx.blockTimestamp > claim.start + claim.deadline then
    let (removed, _) ← removeStoredClaim state.bounty account bountyId
    some (⟨removed, state.proposals⟩, .expired)
  else
    if account != ctx.predecessor then none else
    let (created, id) ← addProposal state.proposals ctx
      (.bountyDone bountyId account) description
    let completed ← completeStoredClaim state.bounty account bountyId
    some (⟨{ completed with locked := created.locked }, created⟩,
      .proposal id)

/-! `bounty_done` is payable even on expired cleanup. For a timely claim,
`add_proposal` enforces the proposal bond and writes its proposal key before
the claim vector; the root is written by the generated outer wrapper. -/
def bountyDoneRawEffect (raw : BountyRawTrie)
    (before : BountyDoneExportState) (after : BountyDoneExportState)
    (account : String) (bountyId : Nat)
    (effect : BountyDoneExportEffect) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes) :
    Option BountyRawTrie :=
  match effect with
  | .expired => bountyRawRemoveClaim raw before.bounty account bountyId
  | .proposal id => do
      let proposal ← proposalAt after.proposals.proposals id
      if (raw (daoProposalEntryKey id)).isSome && !oldProposalDecoded then
        none else pure ()
      let proposalRaw := bountyRawWrite raw (daoProposalEntryKey id)
        (encodeProposal proposal)
      bountyRawCompleteClaim proposalRaw before.bounty account bountyId

def runBountyDoneExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (bountyId : Nat) (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes) :
    Option (BountyRawTrie × BountyDoneExportEffect) := do
  let before ← state
  let bodyCtx : ProposalCreateContext :=
    ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
      wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
  let (after, effect) ← bountyDoneStored before bodyCtx target
    bountyId description
  let account := target.getD wrapper.predecessor
  let afterRaw ← bountyDoneRawEffect raw before after account bountyId
    effect oldProposalDecoded encodeProposal
  let final ← runGeneratedCallWrapper raw "bounty_done"
    { wrapper with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot after))
  some (final, effect)

end SputnikDAO2
