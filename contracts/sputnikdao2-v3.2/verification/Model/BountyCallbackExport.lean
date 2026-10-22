import Model.CallbackExport
import Model.BountyPayoutExecution

namespace SputnikDAO2

/-! `BountyDone` branch of `on_proposal_callback`. A successful promise result
changes the bounty's `times` entry before the proposal entry is rewritten;
failure only rewrites the proposal. The serializers for the complete bounty,
proposal and Contract root remain explicit refinement inputs. -/

def bountyCallbackRaw (raw : BountyRawTrie)
    (proposalId bountyId : Nat) (result : CallbackResult)
    (outcome : BountyPayoutCallbackOutcome)
    (encodeBounty encodeProposal :
      BountyPayoutCallbackOutcome → BountyBytes) : BountyRawTrie :=
  let afterBounty :=
    if result == .success then
      match outcome.state.times with
      | none => bountyRawRemove raw (daoBountyEntryKey bountyId)
      | some _ => bountyRawWrite raw (daoBountyEntryKey bountyId)
          (encodeBounty outcome)
    else raw
  bountyRawWrite afterBounty (daoProposalEntryKey proposalId)
    (encodeProposal outcome)

def runBountyCallbackExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BountyResolutionState)
    (proposalPresent : Bool) (proposalId bountyId resultCount : Nat)
    (result : CallbackResult) (policy : BondPolicyAmounts)
    (proposer : String)
    (encodeBounty encodeProposal encodeRoot :
      BountyPayoutCallbackOutcome → BountyBytes) :
    Option (BountyRawTrie × BountyPayoutCallbackOutcome) := do
  if proposalId ≥ 256 ^ 8 || bountyId ≥ 256 ^ 8 then none else pure ()
  let before ← state
  let outcome ← finishBountyPayout before proposalPresent
    (ctx.current == ctx.predecessor) resultCount result policy proposer
  let afterRaw := bountyCallbackRaw raw proposalId bountyId result
    outcome encodeBounty encodeProposal
  let final ← runGeneratedCallWrapper raw "on_proposal_callback"
    { ctx with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot outcome))
  some (final, outcome)

end SputnikDAO2
