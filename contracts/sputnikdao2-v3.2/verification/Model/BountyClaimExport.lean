import Model.ExportWrapper
import Model.BountyTrie

namespace SputnikDAO2

/-! Payable `bounty_claim` composition. `bounty` and `policyBond` represent
successful LookupMap/policy loads, including their decoding; `state` is the
decoded root and claim/count projection. The wrapper supplies caller and
deposit. Complete Contract serialization remains explicit. -/

def runBountyClaimExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BountyStorageState)
    (bounty : Option (Nat × Nat)) (policyBond : Option Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    Option BountyRawTrie := do
  let before ← state
  let (maxDeadline, times) ← bounty
  let bond ← policyBond
  let after ← addStoredClaim before ctx.predecessor bountyId now
    deadline maxDeadline times bond ctx.attachedDeposit
  let afterRaw := bountyRawAddClaim raw before ctx.predecessor
    bountyId now deadline ctx.attachedDeposit
  runGeneratedCallWrapper raw "bounty_claim"
    { ctx with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot after))

end SputnikDAO2
