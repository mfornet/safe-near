import Model.Methods

namespace SputnikFactory.Spec

def findAccount : List Account → Account → Option Nat
  | [], _ => none
  | head :: tail, query =>
    if head == query then some 0 else (findAccount tail query).map Nat.succ

def daoHeader (order : List Account) : SetHeader :=
  { initialSet with elements := { initialSet.elements with length := order.length } }

/-- Canonical legacy-set representation. It is a conditional invariant: raw code
at a DAO membership key would violate the index clause. The vector order is
explicit because later deletion can swap entries and raw-key aliasing can make
the vector contain duplicates. -/
structure DaoLayout (raw : Raw) (order : List Account) : Prop where
  unique : order.Nodup
  state : read raw stateKey = some (Borsh.encodeSet (daoHeader order))
  index : ∀ account, read raw (daoIndexKey account) =
    (findAccount order account).map (leBytes 8)
  element : ∀ i, i < order.length →
    read raw (daoElementKey i) = (order[i]?).map borshString

/-- Getter coherence needs the header and vector records, but no membership
indexes or uniqueness. This remains applicable after raw code writes alias a
DAO membership key and a later callback appends a duplicate vector entry. -/
structure DaoVectorLayout (raw : Raw) (order : List Account) : Prop where
  state : read raw stateKey = some (Borsh.encodeSet (daoHeader order))
  element : ∀ i, i < order.length →
    read raw (daoElementKey i) = (order[i]?).map borshString

def selectAccounts (order : List Account) : List Nat → Option (List Account)
  | [] => some []
  | index :: indexes => do
    let account ← order[index]?
    let rest ← selectAccounts order indexes
    pure (account :: rest)

def findHash : List (Hash × Metadata) → Hash → Option Nat
  | [], _ => none
  | (head, _) :: tail, query =>
    if head == query then some 0 else (findHash tail query).map Nat.succ

def metadataHeader (order : List (Hash × Metadata)) : MapHeader :=
  { initialMap with
    keys := { initialMap.keys with length := order.length },
    values := { initialMap.values with length := order.length } }

/-- Canonical map representation preserves insertion/swap order and both vector
lengths. A raw code key cannot overlap these canonical map keys by length. -/
structure MetadataLayout (raw : Raw) (order : List (Hash × Metadata)) : Prop where
  unique : (order.map Prod.fst).Nodup
  header : read raw metadataKey = some (Borsh.encodeMap (metadataHeader order))
  index : ∀ hash, read raw (mapIndexKey initialMap hash) =
    (findHash order hash).map (leBytes 8)
  key : ∀ i, i < order.length →
    read raw (vectorKey initialMap.keys i) = (order[i]?).map (fun entry => entry.1.val)
  value : ∀ i, i < order.length →
    read raw (vectorKey initialMap.values i) =
      (order[i]?).map (fun entry => Borsh.encodeMetadata entry.2)

def MetadataBounded (value : Metadata) : Prop :=
  value.commit.toUTF8.data.toList.length < 256 ^ 4 ∧
  ∀ text, value.changelog = some text →
    text.toUTF8.data.toList.length < 256 ^ 4

def selectEntries (order : List (Hash × Metadata)) :
    List Nat → Option (List (Hash × Metadata))
  | [] => some []
  | i :: indexes => do
    let entry ← order[i]?
    let rest ← selectEntries order indexes
    pure (entry :: rest)

end SputnikFactory.Spec
