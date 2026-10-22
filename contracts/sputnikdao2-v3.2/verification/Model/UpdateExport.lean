import Model.ExportWrapper
import Model.Upgrade
import Model.FactoryEncoding

namespace SputnikDAO2

structure RawUpdateContext where
  current : String
  predecessor : String
  attachedDeposit : Nat
  successfulPromiseResult : Option CodeBytes
  rawInput : Option CodeBytes
  deriving Repr, DecidableEq

-- `FactoryInfo::try_from_slice` and AccountId parsing are refinement inputs.
-- Unlike generated calls, the manual export reads FACTORY directly and does
-- not load the Contract root or impose a nonpayable deposit guard.
def factoryReadFromRaw (raw : BountyRawTrie)
    (decodeFactory : BountyBytes → Option FactoryInfo) : FactoryRead :=
  match raw daoFactoryKey with
  | none => .missing
  | some bytes =>
      match decodeFactory bytes with
      | none => .malformed
      | some info => .stored info

def validatedFactoryParent (current : String)
    (validAccount : String → Bool) : Option String := do
  let parent ← factoryParentSuffix current
  if validAccount parent then some parent else none

def runRawUpdateExport (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool)
    (hashCode : CodeBytes → String) : Option UpgradeReceipt :=
  if findDAOExport "update" != some ⟨"update", .raw, false, false⟩ then
    none
  else
    runUpdate hashCode
      { current := ctx.current
        predecessor := ctx.predecessor
        factoryRead := factoryReadFromRaw raw decodeFactory
        fallbackFactory := validatedFactoryParent ctx.current validAccount
        successfulPromiseResult := ctx.successfulPromiseResult
        rawInput := ctx.rawInput }

def runParsedUpdateExport (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool)
    (hashCode : CodeBytes → String) : Option UpgradeReceipt :=
  runRawUpdateExport raw ctx (parseFactoryInfoExact validAccount)
    validAccount hashCode

end SputnikDAO2
