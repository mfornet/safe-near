import Model.Types

namespace SputnikFactory.Borsh

export NearSdk.Borsh (fromLE)
export NearSdk.BorshParse (Parser take natural bytes text optionalText exact)
export NearSdk.Collections (vector setHeader mapHeader encodeVector encodeSet encodeMap)

def metadata : Parser Metadata := fun input => do
  let major :: minor :: rest := input | none
  let (commit, rest) ← text rest
  let (changelog, rest) ← optionalText rest
  pure (⟨major, minor, commit, changelog⟩, rest)

def hash (input : Bytes) : Option Hash :=
  if h : input.length = 32 then some ⟨input, h⟩ else none

def account (input : Bytes) : Option Account := do
  let value ← exact text input
  if validAccount value then some value else none

def encodeMetadata (value : Metadata) : Bytes :=
  [value.major, value.minor] ++ borshString value.commit ++
    match value.changelog with | none => [0] | some text => 1 :: borshString text

end SputnikFactory.Borsh
