import Model.FactoryViewRefinement
import Model.BlobKeySeparation

namespace SputnikDAO2

/-! Conditional approved `FactoryInfoUpdate` branch of `act_proposal`.
`approvedBody` stands for proposal decoding, kind equality, permission,
vote/finalize status and synchronous execution. The concrete proposal and
root serializers are explicit inputs. On that branch, source writes FACTORY,
then the updated proposal, and the generated wrapper writes STATE. -/
def runApprovedFactoryInfoUpdateExport (raw : BountyRawTrie)
    (wrapper : CallWrapperContext) (stateDecoded approvedBody : Bool)
    (id : Nat) (info : FactoryInfo)
    (proposalBytes rootBytes : BountyBytes) : Option BountyRawTrie := do
  if id > maxU64 || !approvedBody then none else pure ()
  let _ ← raw (daoProposalEntryKey id)
  let afterFactory := bountyRawWrite raw daoFactoryKey
    (encodeFactoryInfo info)
  let afterProposal := bountyRawWrite afterFactory
    (daoProposalEntryKey id) proposalBytes
  runGeneratedCallWrapper raw "act_proposal"
    { wrapper with stateDecoded := stateDecoded }
    (some (afterProposal, rootBytes))

end SputnikDAO2
