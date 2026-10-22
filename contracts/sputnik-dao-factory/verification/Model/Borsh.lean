import Model.Types

namespace SputnikFactory.Borsh

abbrev Parser (α : Type) := Bytes → Option (α × Bytes)

def fromLE : Bytes → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * fromLE rest

def take (count : Nat) : Parser Bytes := fun input =>
  if count ≤ input.length then some (input.take count, input.drop count) else none

def natural (width : Nat) : Parser Nat := fun input => do
  let (bytes, rest) ← take width input
  pure (fromLE bytes, rest)

def bytes : Parser Bytes := fun input => do
  let (count, rest) ← natural 4 input
  take count rest

def text : Parser String := fun input => do
  let (raw, rest) ← bytes input
  let value ← String.fromUTF8? ⟨raw.toArray⟩
  pure (value, rest)

def optionalText : Parser (Option String) := fun input => do
  match input with
  | 0 :: rest => pure (none, rest)
  | 1 :: rest => do
    let (value, tail) ← text rest
    pure (some value, tail)
  | _ => none

def vector : Parser VectorHeader := fun input => do
  let (count, rest) ← natural 8 input
  let (keyPrefix, rest) ← bytes rest
  pure (⟨count, keyPrefix⟩, rest)

def setHeader : Parser SetHeader := fun input => do
  let (keyPrefix, rest) ← bytes input
  let (elements, rest) ← vector rest
  pure (⟨keyPrefix, elements⟩, rest)

def mapHeader : Parser MapHeader := fun input => do
  let (keyPrefix, rest) ← bytes input
  let (keys, rest) ← vector rest
  let (values, rest) ← vector rest
  pure (⟨keyPrefix, keys, values⟩, rest)

def metadata : Parser Metadata := fun input => do
  let major :: minor :: rest := input | none
  let (commit, rest) ← text rest
  let (changelog, rest) ← optionalText rest
  pure (⟨major, minor, commit, changelog⟩, rest)

def exact (parser : Parser α) (input : Bytes) : Option α := do
  let (value, rest) ← parser input
  if rest.isEmpty then some value else none

def hash (input : Bytes) : Option Hash :=
  if h : input.length = 32 then some ⟨input, h⟩ else none

def account (input : Bytes) : Option Account := do
  let value ← exact text input
  if validAccount value then some value else none

def encodeVector (header : VectorHeader) : Bytes :=
  leBytes 8 header.length ++ borshBytes header.keyPrefix

def encodeSet (header : SetHeader) : Bytes :=
  borshBytes header.indexPrefix ++ encodeVector header.elements

def encodeMap (header : MapHeader) : Bytes :=
  borshBytes header.indexPrefix ++ encodeVector header.keys ++ encodeVector header.values

def encodeMetadata (value : Metadata) : Bytes :=
  [value.major, value.minor] ++ borshString value.commit ++
    match value.changelog with | none => [0] | some text => 1 :: borshString text

end SputnikFactory.Borsh
