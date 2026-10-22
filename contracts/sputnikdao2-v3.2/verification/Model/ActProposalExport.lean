import Model.ExportWrapper
import Model.ProposalAct
import Model.BlobKeySeparation

namespace SputnikDAO2

/-! Non-vote `act_proposal` export projection. The decoded proposal map and
permission/kind decisions are inputs; `policyReadable` represents the
LazyOption unwrap and policy-version conversion before those checks. The
global log is in the projected root, while only RemoveProposal changes the
proposal LookupMap key. -/
def nonVoteRawEffect (raw : BountyRawTrie) (id : Nat)
    (action : NonVoteAction) : BountyRawTrie :=
  match action with
  | .removeProposal => bountyRawRemove raw (daoProposalEntryKey id)
  | .moveToHub | .addProposal => raw

def runActNonVoteExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option NonVoteState)
    (ctx : NonVoteContext) (policyReadable : Bool)
    (id : Nat) (action : NonVoteAction)
    (encodeRoot : NonVoteState → BountyBytes) : Option BountyRawTrie := do
  let before ← state
  if id > maxU64 || !policyReadable then none else
  let bodyCtx : NonVoteContext :=
    ⟨wrapper.predecessor, ctx.blockHeight,
      ctx.permissionAllowed, ctx.exactKindMatches⟩
  let after ← actNonVote before bodyCtx id action
  let afterRaw := nonVoteRawEffect raw id action
  runGeneratedCallWrapper raw "act_proposal"
    { wrapper with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot after))

end SputnikDAO2
