import Model.ExportWrapper
import Model.Views
import Model.Upgrade

namespace SputnikDAO2

/-! Named view compositions. `decoded` contains the relevant projection of
the deserialized Contract root and, for delegation, the decoded LookupMap
entry. Host balance, storage usage and storage price are explicit inputs.
JSON argument and return codecs remain external. -/

def runLockedStorageView (raw : BountyRawTrie) (decoded : Option Unit)
    (deposit byteCost usage : Nat) : Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_locked_storage_amount" decoded deposit
    (fun _ _ => viewLockedStorage byteCost usage)

def runAvailableView (raw : BountyRawTrie) (lockedDecoded : Option Nat)
    (deposit balance byteCost usage : Nat) : Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_available_amount" lockedDecoded deposit
    (fun locked _ => viewAvailable balance byteCost usage locked)

def runDelegationSupplyView (raw : BountyRawTrie)
    (totalDecoded : Option Nat) (deposit : Nat) :
    Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "delegation_total_supply"
    totalDecoded deposit (fun total _ => total)

def runDelegationBalanceView (raw : BountyRawTrie)
    (entryDecoded : Option (Option Nat)) (deposit : Nat) :
    Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "delegation_balance_of"
    entryDecoded deposit (fun entry _ => viewDelegationBalance entry)

def runDelegationRatioView (raw : BountyRawTrie)
    (decoded : Option (Option Nat × Nat)) (deposit : Nat) :
    Option ((Nat × Nat) × BountyRawTrie) :=
  runGeneratedViewWrapper raw "delegation_balance_ratio"
    decoded deposit (fun pair _ => viewDelegationRatio pair.1 pair.2)

def runHasBlobView (raw : BountyRawTrie) (decoded : Option Unit)
    (deposit : Nat) (digest : BountyBytes) :
    Option (Bool × BountyRawTrie) :=
  if digest.length != 32 then none
  else runGeneratedViewWrapper raw "has_blob" decoded deposit
    (fun _ trie => (trie digest).isSome)

def runVersionView (raw : BountyRawTrie) (decoded : Option Unit)
    (deposit : Nat) : Option (String × BountyRawTrie) :=
  runGeneratedViewWrapper raw "version" decoded deposit
    (fun _ _ => viewVersion)

def runConfigView {α : Type} (raw : BountyRawTrie)
    (decoded : Option (Option α)) (deposit : Nat) :
    Option (α × BountyRawTrie) := do
  let stored ← decoded
  let config ← readConfig stored
  runGeneratedViewWrapper raw "get_config" (some config) deposit
    (fun value _ => value)

def runPolicyView {α : Type} (raw : BountyRawTrie)
    (decoded : Option (Option (StoredPolicy α))) (deposit : Nat) :
    Option (α × BountyRawTrie) := do
  let stored ← decoded
  let policy ← (readPolicy stored).toOption
  runGeneratedViewWrapper raw "get_policy" (some policy) deposit
    (fun value _ => value)

def runNamedStakingView (raw : BountyRawTrie)
    (decoded : Option (Option String)) (deposit : Nat) :
    Option (String × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_staking_contract" decoded deposit
    (fun staking _ => viewStakingContract staking)

def runFactoryInfoView (raw : BountyRawTrie) (decoded : Option Unit)
    (deposit : Nat) (factoryRead : FactoryRead) (current : String) :
    Option (FactoryInfo × BountyRawTrie) := do
  let _ ← decoded
  let info ← factoryInfoForAccount factoryRead current
  runGeneratedViewWrapper raw "get_factory_info" (some info) deposit
    (fun value _ => value)

def runLastProposalIdView (raw : BountyRawTrie)
    (decoded : Option Nat) (deposit : Nat) :
    Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_last_proposal_id" decoded deposit
    (fun id _ => id)

def runLastBountyIdView (raw : BountyRawTrie)
    (decoded : Option Nat) (deposit : Nat) :
    Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_last_bounty_id" decoded deposit
    (fun id _ => id)

def runProposalsView {α : Type} (raw : BountyRawTrie)
    (decodedLastId : Option Nat) (deposit fromIndex limit : Nat)
    (lookup : Nat → Option α) :
    Option (List (Nat × α) × BountyRawTrie) := do
  let lastId ← decodedLastId
  let page ← viewPage lastId fromIndex limit lookup
  runGeneratedViewWrapper raw "get_proposals" (some page) deposit
    (fun value _ => value)

def runBountiesView {α : Type} (raw : BountyRawTrie)
    (decodedLastId : Option Nat) (deposit fromIndex limit : Nat)
    (lookup : Nat → Option α) :
    Option (List (Nat × α) × BountyRawTrie) := do
  let lastId ← decodedLastId
  let page ← viewPage lastId fromIndex limit lookup
  runGeneratedViewWrapper raw "get_bounties" (some page) deposit
    (fun value _ => value)

def runProposalView {α : Type} (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit id : Nat) (entry : Option α) :
    Option ((Nat × α) × BountyRawTrie) := do
  let _ ← decoded
  let value ← viewOne id entry
  runGeneratedViewWrapper raw "get_proposal" (some value) deposit
    (fun pair _ => pair)

def runBountyView {α : Type} (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit id : Nat) (entry : Option α) :
    Option ((Nat × α) × BountyRawTrie) := do
  let _ ← decoded
  let value ← viewOne id entry
  runGeneratedViewWrapper raw "get_bounty" (some value) deposit
    (fun pair _ => pair)

def runBountyClaimsView {α : Type} (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit : Nat)
    (claims : Option (List α)) : Option (List α × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_bounty_claims" decoded deposit
    (fun _ _ => viewBountyClaims claims)

def runBountyClaimCountView (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit : Nat) (count : Option Nat) :
    Option (Nat × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_bounty_number_of_claims"
    decoded deposit (fun _ _ => viewBountyClaimCount count)

def runActionsLogView {α : Type} (raw : BountyRawTrie)
    (decoded : Option (List α)) (deposit : Nat) :
    Option (List α × BountyRawTrie) :=
  runGeneratedViewWrapper raw "get_actions_log" decoded deposit
    (fun entries _ => entries)

end SputnikDAO2
