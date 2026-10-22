import Model.PolicyReadBarrier
import Model.BountyClaimExport
import Model.BountyGiveupExport
import Model.BountyDoneExport

namespace SputnikDAO2

def runRawPolicyBountyClaimExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BountyStorageState)
    (bounty : Option (Nat × Nat)) (policyBond : Option Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    Option BountyRawTrie :=
  if policyReadableFromRaw raw then
    runBountyClaimExport raw ctx state bounty policyBond bountyId now
      deadline encodeRoot
  else none

def runRawPolicyBountyGiveupExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BountyStorageState)
    (policy : Option (Nat × Nat)) (bountyId now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    Option (BountyRawTrie × Option Nat) :=
  if policyReadableFromRaw raw then
    runBountyGiveupExport raw ctx state policy bountyId now encodeRoot
  else none

/-! The expired `bounty_done` branch performs claim cleanup without reading
policy. Its timely branch invokes `add_proposal`, which does read policy. The
source may attempt writes before a failing nested call; host rollback remains
an external obligation. -/
def runRawPolicyBountyDoneExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (state : Option BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (bountyId : Nat) (description : String) (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes) :
    Option (BountyRawTrie × BountyDoneExportEffect) := do
  let (final, effect) ← runBountyDoneExport raw wrapper state create target
    bountyId description oldProposalDecoded encodeProposal encodeRoot
  match effect with
  | .expired => some (final, effect)
  | .proposal _ =>
      if policyReadableFromRaw raw then some (final, effect) else none

end SputnikDAO2
