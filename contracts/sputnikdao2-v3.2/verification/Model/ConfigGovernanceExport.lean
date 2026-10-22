import Model.ExportWrapper
import Model.BlobKeySeparation
import Model.ConfigPolicyDecoding

namespace SputnikDAO2

/-! Approved ChangeConfig branch after the action's policy, kind and status
checks. near-sdk `LazyOption::set` writes key 0 without decoding its previous
bytes, then `act_proposal` stores the proposal and its wrapper stores STATE.
Complete proposal/root serialization remains an explicit input. -/
def runApprovedChangeConfigExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (stateDecoded approvedBody : Bool)
    (id : Nat) (config : WireConfig)
    (proposalBytes rootBytes : BountyBytes) : Option BountyRawTrie := do
  if id > maxU64 || !approvedBody then none else pure ()
  let _ ← raw (daoProposalEntryKey id)
  let afterConfig := bountyRawWrite raw daoConfigKey
    (encodeWireConfig config)
  let afterProposal := bountyRawWrite afterConfig
    (daoProposalEntryKey id) proposalBytes
  runGeneratedCallWrapper raw "act_proposal"
    { wrapper with stateDecoded := stateDecoded }
    (some (afterProposal, rootBytes))

-- `get_config` first requires a decoded root, then reads the LazyOption at
-- key 0 and unwraps it. Missing or malformed bytes abort the view.
def runParsedConfigView (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit : Nat) :
    Option (WireConfig × BountyRawTrie) := do
  let _ ← decoded
  let bytes ← raw daoConfigKey
  let config ← parseWireConfigExact bytes
  runGeneratedViewWrapper raw "get_config" (some config) deposit
    (fun value _ => value)

end SputnikDAO2
