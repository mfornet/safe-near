import Model.ConfigPolicyDecoding
import Model.Initialize

namespace SputnikDAO2

-- Borsh AccountId is a length-prefixed UTF-8 string whose validity is
-- checked by near-sdk. The validator remains an explicit refinement input.
def parseFactoryInfo (validAccount : String → Bool) :
    BountyParser FactoryInfo := fun input => do
  let (factoryId, rest) ← parseWireString input
  if !validAccount factoryId then none else pure ()
  let (autoUpdate, rest) ← bountyParseBool rest
  some (⟨factoryId, autoUpdate⟩, rest)

def parseFactoryInfoExact (validAccount : String → Bool)
    (bytes : BountyBytes) : Option FactoryInfo := do
  let (info, rest) ← parseFactoryInfo validAccount bytes
  if rest.isEmpty then some info else none

end SputnikDAO2
