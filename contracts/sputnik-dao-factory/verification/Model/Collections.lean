import Model.Transaction
import Model.Borsh

namespace SputnikFactory

export NearSdk.Collections (vectorKey)

def vectorGet (header : VectorHeader) (index : Nat) : Tx (Option Bytes) := do
  if index ≥ header.length then pure none else
    let bytes ← load (vectorKey header index)
    let value ← expect bytes .missingElement
    pure (some value)

def vectorReplace (header : VectorHeader) (index : Nat) (value : Bytes) : Tx Bytes := do
  require (index < header.length) .invalidIndex
  let previous ← expect (← load (vectorKey header index)) .missingElement
  save (vectorKey header index) value
  pure previous

def vectorPush (header : VectorHeader) (value : Bytes) : Tx VectorHeader := do
  save (vectorKey header header.length) value
  require (header.length + 1 < u64Bound) .overflow
  pure { header with length := header.length + 1 }

def vectorPop (header : VectorHeader) : Tx (Option (Bytes × VectorHeader)) := do
  if header.length = 0 then pure none else
    let index := header.length - 1
    let previous ← expect (← load (vectorKey header index)) .missingElement
    erase (vectorKey header index)
    pure (some (previous, { header with length := index }))

/-- Exact successful state effect of SDK swap_remove_raw, including validation
that the original element existed and preserving the removed raw value. -/
def vectorSwapRemove (header : VectorHeader) (index : Nat) : Tx (Bytes × VectorHeader) := do
  require (index < header.length) .invalidIndex
  if index + 1 = header.length then
    expect (← vectorPop header) .inconsistent
  else
    let (last, reduced) ← expect (← vectorPop header) .inconsistent
    let previous ← vectorReplace reduced index last
    pure (previous, reduced)

def setIndexKey (header : SetHeader) (account : Account) : Bytes :=
  header.indexPrefix ++ borshString account

def setContains (header : SetHeader) (account : Account) : Tx Bool := do
  pure (← load (setIndexKey header account)).isSome

def setInsert (header : SetHeader) (account : Account) : Tx SetHeader := do
  if (← setContains header account) then pure header else
    save (setIndexKey header account) (leBytes 8 header.elements.length)
    let elements ← vectorPush header.elements (borshString account)
    pure { header with elements }

def accountsAt (header : VectorHeader) : List Nat → Tx (List Account)
  | [] => pure []
  | index :: indexes => do
    let value ← vectorGet header index
    match value with
    | none => accountsAt header indexes
    | some bytes =>
      let account ← expect (Borsh.account bytes) .invalidAccount
      let rest ← accountsAt header indexes
      pure (account :: rest)

def mapLength (header : MapHeader) : Tx Nat := do
  require (header.keys.length == header.values.length) .inconsistent
  pure header.keys.length

def mapIndexKey (header : MapHeader) (hash : Hash) : Bytes := header.indexPrefix ++ hash.val

def mapGet (header : MapHeader) (hash : Hash) : Tx (Option Metadata) := do
  match ← load (mapIndexKey header hash) with
  | none => pure none
  | some rawIndex =>
    let index ← expect (Borsh.exact (Borsh.natural 8) rawIndex) .invalidIndex
    let bytes ← expect (← vectorGet header.values index) .inconsistent
    let value ← expect (Borsh.exact Borsh.metadata bytes) .invalidMetadata
    pure (some value)

def mapInsert (header : MapHeader) (hash : Hash) (metadata : Metadata) : Tx MapHeader := do
  match ← load (mapIndexKey header hash) with
  | some rawIndex =>
    let index ← expect (Borsh.exact (Borsh.natural 8) rawIndex) .invalidIndex
    let previous ← vectorReplace header.values index (Borsh.encodeMetadata metadata)
    -- UnorderedMap::insert deserializes its returned old value even if ignored.
    let _ ← expect (Borsh.exact Borsh.metadata previous) .invalidMetadata
    pure header
  | none =>
    let count ← mapLength header
    save (mapIndexKey header hash) (leBytes 8 count)
    let keys ← vectorPush header.keys hash.val
    let values ← vectorPush header.values (Borsh.encodeMetadata metadata)
    pure { header with keys, values }

def mapRemove (header : MapHeader) (hash : Hash) : Tx MapHeader := do
  match ← load (mapIndexKey header hash) with
  | none => pure header
  | some rawIndex =>
    let count ← mapLength header
    if count = 1 then erase (mapIndexKey header hash) else
      require (count > 0) .overflow
      let last ← expect (← vectorGet header.keys (count - 1)) .inconsistent
      erase (mapIndexKey header hash)
      if last != hash.val then save (header.indexPrefix ++ last) rawIndex
    let index ← expect (Borsh.exact (Borsh.natural 8) rawIndex) .invalidIndex
    let (_, keys) ← vectorSwapRemove header.keys index
    let (previous, values) ← vectorSwapRemove header.values index
    let _ ← expect (Borsh.exact Borsh.metadata previous) .invalidMetadata
    pure { header with keys, values }

def metadataAt (header : MapHeader) : List Nat → Tx (List (Hash × Metadata))
  | [] => pure []
  | index :: indexes => do
    let keyBytes ← expect (← vectorGet header.keys index) .inconsistent
    let hash ← expect (Borsh.hash keyBytes) .invalidIndex
    let valueBytes ← expect (← vectorGet header.values index) .inconsistent
    let metadata ← expect (Borsh.exact Borsh.metadata valueBytes) .invalidMetadata
    let rest ← metadataAt header indexes
    pure ((hash, metadata) :: rest)

end SputnikFactory
