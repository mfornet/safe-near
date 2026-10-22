import Model.ViewExport
import Model.UpdateExport

namespace SputnikDAO2

-- Shared resolution for `get_factory_info` and the manual `update` export.
-- The near-sdk AccountId predicate is an explicit input in both paths.
def readFactoryInfoFromRaw (raw : BountyRawTrie) (current : String)
    (validAccount : String → Bool) : Option FactoryInfo :=
  effectiveFactory
    (factoryReadFromRaw raw (parseFactoryInfoExact validAccount))
    (validatedFactoryParent current validAccount)

def runParsedFactoryInfoView (raw : BountyRawTrie)
    (decoded : Option Unit) (deposit : Nat) (current : String)
    (validAccount : String → Bool) :
    Option (FactoryInfo × BountyRawTrie) := do
  let _ ← decoded
  let info ← readFactoryInfoFromRaw raw current validAccount
  runGeneratedViewWrapper raw "get_factory_info" (some info) deposit
    (fun value _ => value)

end SputnikDAO2
