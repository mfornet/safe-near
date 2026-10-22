import Model.ExportWrapper
import Model.BlobKeySeparation
import Model.ConfigPolicyDecoding

namespace SputnikDAO2

/-! Conditional approved ChangePolicy execution. Public add_proposal rejects
Default, but a synthetic pre-existing proposal can still execute it. The
source reads the CURRENT policy before reaching LazyOption::set, so existing
key 1 bytes must decode as Current. The later set overwrites key 1 without
another old-value decode, then stores the proposal and generated root. -/
def policyReadableFromRaw (raw : BountyRawTrie) : Bool :=
  match raw daoPolicyKey with
  | none => false
  | some bytes =>
      match parseWirePolicyExact bytes with
      | some (.current _) => true
      | _ => false

def runApprovedChangePolicyExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (stateDecoded approvedBody : Bool)
    (id : Nat) (policy : WireVersionedPolicy)
    (proposalBytes rootBytes : BountyBytes) : Option BountyRawTrie := do
  if id > maxU64 || !approvedBody ||
      !policyReadableFromRaw raw then none else pure ()
  let _ ← raw (daoProposalEntryKey id)
  let afterPolicy := bountyRawWrite raw daoPolicyKey
    (encodeWireVersionedPolicy policy)
  let afterProposal := bountyRawWrite afterPolicy
    (daoProposalEntryKey id) proposalBytes
  runGeneratedCallWrapper raw "act_proposal"
    { wrapper with stateDecoded := stateDecoded }
    (some (afterProposal, rootBytes))

-- `get_policy` unwraps the LazyOption and converts VersionedPolicy to the
-- current Policy. Its Default conversion panics in the pinned source.
def runParsedPolicyView (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit : Nat) :
    Option (WirePolicy × BountyRawTrie) := do
  let _ ← decoded
  let bytes ← raw daoPolicyKey
  let stored ← parseWirePolicyExact bytes
  let policy ← match stored with
    | .current policy => some policy
    | .default _ => none
  runGeneratedViewWrapper raw "get_policy" (some policy) deposit
    (fun value _ => value)

end SputnikDAO2
