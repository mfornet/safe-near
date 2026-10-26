import NearSdk.BorshParse

/-!
# near-sdk collections

The persistent layout of near-sdk's `Vector`, `UnorderedSet` and
`UnorderedMap`: the header each stores in the contract state, how a header is
encoded, and the key of an element.
-/

namespace NearSdk.Collections
open NearSdk.Borsh NearSdk.BorshParse

/-- `Vector`: its length and the prefix its element keys start with. -/
structure VectorHeader where
  length : Nat
  keyPrefix : Bytes
  deriving DecidableEq, Repr

/-- `UnorderedSet`: the prefix of its element index, and its elements. -/
structure SetHeader where
  indexPrefix : Bytes
  elements : VectorHeader
  deriving DecidableEq, Repr

/-- `UnorderedMap`: the prefix of its key index, its keys and its values. -/
structure MapHeader where
  indexPrefix : Bytes
  keys : VectorHeader
  values : VectorHeader
  deriving DecidableEq, Repr

/-- `Vector` keys are the raw little-endian index appended to its key prefix. -/
def vectorKey (header : VectorHeader) (index : Nat) : Bytes :=
  header.keyPrefix ++ leBytes 8 index

def encodeVector (header : VectorHeader) : Bytes :=
  leBytes 8 header.length ++ Borsh.bytes header.keyPrefix

def encodeSet (header : SetHeader) : Bytes :=
  Borsh.bytes header.indexPrefix ++ encodeVector header.elements

def encodeMap (header : MapHeader) : Bytes :=
  Borsh.bytes header.indexPrefix ++ encodeVector header.keys ++ encodeVector header.values

def vector : Parser VectorHeader := fun input => do
  let (count, rest) ← natural 8 input
  let (keyPrefix, rest) ← BorshParse.bytes rest
  pure (⟨count, keyPrefix⟩, rest)

def setHeader : Parser SetHeader := fun input => do
  let (keyPrefix, rest) ← BorshParse.bytes input
  let (elements, rest) ← vector rest
  pure (⟨keyPrefix, elements⟩, rest)

def mapHeader : Parser MapHeader := fun input => do
  let (keyPrefix, rest) ← BorshParse.bytes input
  let (keys, rest) ← vector rest
  let (values, rest) ← vector rest
  pure (⟨keyPrefix, keys, values⟩, rest)

theorem vector_encode (header : VectorHeader) (rest : Bytes)
    (hlen : header.length < 256 ^ 8)
    (hprefix : header.keyPrefix.length < 256 ^ 4) :
    vector (encodeVector header ++ rest) = some (header, rest) := by
  cases header with
  | mk length keyPrefix =>
    simp [vector, encodeVector, natural_encode, bytes_encode, hlen, hprefix, List.append_assoc]

theorem set_encode (header : SetHeader) (rest : Bytes)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4) :
    setHeader (encodeSet header ++ rest) = some (header, rest) := by
  cases header with
  | mk indexPrefix elements =>
    simp [setHeader, encodeSet, List.append_assoc, bytes_encode, vector_encode, hindex, hlen, hprefix]

theorem map_encode (header : MapHeader) (rest : Bytes)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hkeys : header.keys.length < 256 ^ 8)
    (hkeyPrefix : header.keys.keyPrefix.length < 256 ^ 4)
    (hvalues : header.values.length < 256 ^ 8)
    (hvaluePrefix : header.values.keyPrefix.length < 256 ^ 4) :
    mapHeader (encodeMap header ++ rest) = some (header, rest) := by
  cases header with
  | mk indexPrefix keys values =>
    simp [mapHeader, encodeMap, List.append_assoc,
      bytes_encode, vector_encode, hindex, hkeys, hkeyPrefix, hvalues, hvaluePrefix]

theorem exact_set_encode (header : SetHeader)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4) :
    exact setHeader (encodeSet header) = some header := by
  have h := set_encode header [] hindex hlen hprefix
  simp only [List.append_nil] at h
  simp [exact, h]

theorem exact_map_encode (header : MapHeader)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hkeys : header.keys.length < 256 ^ 8)
    (hkeyPrefix : header.keys.keyPrefix.length < 256 ^ 4)
    (hvalues : header.values.length < 256 ^ 8)
    (hvaluePrefix : header.values.keyPrefix.length < 256 ^ 4) :
    exact mapHeader (encodeMap header) = some header := by
  have h := map_encode header [] hindex hkeys hkeyPrefix hvalues hvaluePrefix
  simp only [List.append_nil] at h
  simp [exact, h]

end NearSdk.Collections
