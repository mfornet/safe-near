import Model.State

/-! SDK 5.17.1 legacy UnorderedMap layout. A logical map has multiple physical
representations because vector order depends on insertion and swap removal.
The order is an explicit witness; it is never guessed by sorting logical keys.
Public keys here are interpreted by a byte assignment, separating the abstract
key model from SDK curve tags and validated public key payloads. -/
namespace Linkdrop.Storage

abbrev Bytes := List UInt8
abbrev Raw := List (Bytes × Bytes)

def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

def vectorBytes (bs : Bytes) : Bytes := leBytes 4 bs.length ++ bs

/-- `PublicKey` is a struct containing Vec<u8>, not the nearcore enum encoding.
Its data contains a curve tag followed by 32 (ED25519) or 64 (SECP256K1) bytes. -/
def validPublicKey (bs : Bytes) : Prop :=
  (bs.head? = some 0 ∧ bs.length = 33) ∨ (bs.head? = some 1 ∧ bs.length = 65)

def stateKey : Bytes := [83, 84, 65, 84, 69]
def indexPrefix : Bytes := [97, 105]
def keysPrefix : Bytes := [97, 107]
def valuesPrefix : Bytes := [97, 118]

/-- UnorderedMap serializes its index prefix, then two Vector headers. -/
def header (count : Nat) : Bytes :=
  vectorBytes indexPrefix ++ leBytes 8 count ++ vectorBytes keysPrefix ++
    leBytes 8 count ++ vectorBytes valuesPrefix

/-- Three trie records per logical map entry: key->index, index->key, index->value. -/
def entry (keyData : Key → Bytes) (s : State) (index : Nat) (key : Key) : Raw :=
  [(indexPrefix ++ vectorBytes (keyData key), leBytes 8 index),
   (keysPrefix ++ leBytes 8 index, vectorBytes (keyData key)),
   (valuesPrefix ++ leBytes 8 index, leBytes 16 ((s.accounts key).getD 0))]

def records (keyData : Key → Bytes) (s : State) : Nat → List Key → Raw
  | _, [] => []
  | i, k :: ks => entry keyData s i k ++ records keyData s (i + 1) ks

def encode (keyData : Key → Bytes) (s : State) (order : List Key) : Raw :=
  if s.initialized then (stateKey, header order.length) :: records keyData s 0 order else []

/-- Preconditions for a physical representation. Values are bounded by State.WF;
order length is u64; unique keys and globally injective byte assignments prevent aliasing, including
with abstract keys absent from the stored order.
Absence of extraneous trie records is imposed by Represents below. -/
def LayoutValid (keyData : Key → Bytes) (s : State) (order : List Key) : Prop :=
  s.WF ∧ order.Nodup ∧ order.length < 2 ^ 64 ∧
  (∀ k, k ∈ order ↔ (s.accounts k).isSome = true) ∧
  (∀ k ∈ order, validPublicKey (keyData k)) ∧
  (∀ k j, keyData k = keyData j → k = j)

/-- Exact trie contents, up to enumeration order. This is a specification relation;
its compatibility with concrete SDK writes remains a separate obligation. -/
def Represents (keyData : Key → Bytes) (raw : Raw) (s : State) : Prop :=
  ∃ order, LayoutValid keyData s order ∧ raw.Perm (encode keyData s order)

/-- Mathematical inverse of the layout relation, as in w-near. Uniqueness is
proved in Proofs.Projection; this is not an executable Borsh decoder. -/
noncomputable def project (keyData : Key → Bytes) (raw : Raw) : Option State := by
  classical
  exact if h : ∃ s, Represents keyData raw s then some (Classical.choose h) else none

def recordBytes (extraBytes : Nat) (r : Bytes × Bytes) : Nat :=
  r.1.length + r.2.length + extraBytes

def usage (extraBytes : Nat) (raw : Raw) : Nat :=
  (raw.map (recordBytes extraBytes)).sum

end Linkdrop.Storage
