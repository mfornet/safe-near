import Model.Boundary.Encoding
import NearInterface.Boundary

/-!
# linkdrop's state and its storage

`LinkDrop { accounts: UnorderedMap<PublicKey, NearToken> }` with prefix `b"a"`,
near-sdk 5.17.1's legacy `collections::UnorderedMap`. Its layout depends on
the order of the two vectors behind it, which insertions and swap removals
determine, so the map is that order: a list of entries. The storage is either
empty (before `new`) or the map: the state is an optional map.

* `STATE`: the map's Borsh header, the index prefix `ai` and the two vector
  headers (length, prefixes `ak` and `av`);
* `ai ++ borsh(key)` → the entry's index (`u64`);
* `ak ++ index` → `borsh(key)`; `av ++ index` → the amount (`u128`).

`borsh(key)` is the key data with a `u32` length. Indices and amounts are
little-endian.
-/

namespace Linkdrop.Boundary

open NearInterface (RawStorage)

/-- The `u128` amounts are yoctoNEAR. -/
def maxAmount : Nat := 2 ^ 128 - 1

/-- The map, in vector order. -/
structure Map where
  entries : List (PublicKey × Nat)

namespace Map

def get (s : Map) (k : PublicKey) : Option Nat := (s.entries.find? (·.1 == k)).map (·.2)

/-- `UnorderedMap::insert`: overwrite in place, or push. -/
def insert (s : Map) (k : PublicKey) (v : Nat) : Map :=
  match s.entries.findIdx? (·.1 == k) with
  | some i => ⟨s.entries.set i (k, v)⟩
  | none => ⟨s.entries ++ [(k, v)]⟩

/-- `UnorderedMap::remove`: swap-remove, moving the last entry into the hole. -/
def remove (s : Map) (k : PublicKey) : Map :=
  match s.entries.findIdx? (·.1 == k) with
  | none => s
  | some i =>
    match s.entries.getLast? with
    | some last => ⟨(s.entries.set i last).dropLast⟩
    | none => s

/-- Distinct keys, `u128` amounts, `u64` length. -/
def Inv (s : Map) : Prop :=
  (s.entries.map (·.1)).Nodup ∧ (∀ e ∈ s.entries, e.2 ≤ maxAmount) ∧ s.entries.length < 2 ^ 64

end Map

/-- Empty storage, or the map. -/
abbrev State := Option Map

def State.Inv : State → Prop
  | none => True
  | some m => m.Inv

/-! ## Storage -/

def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

def borshBytes (bs : Bytes) : Bytes := leBytes 4 bs.length ++ bs

def stateKey : Bytes := "STATE".toUTF8.toList
def indexPrefix : Bytes := "ai".toUTF8.toList
def keysPrefix : Bytes := "ak".toUTF8.toList
def valuesPrefix : Bytes := "av".toUTF8.toList

/-- `UnorderedMap { key_index_prefix, keys: Vector { len, prefix }, values: Vector { len, prefix } }`. -/
def header (count : Nat) : Bytes :=
  borshBytes indexPrefix ++ leBytes 8 count ++ borshBytes keysPrefix ++
    leBytes 8 count ++ borshBytes valuesPrefix

def entryRecords (index : Nat) (e : PublicKey × Nat) : List (Bytes × Bytes) :=
  [(indexPrefix ++ borshBytes e.1.val, leBytes 8 index),
   (keysPrefix ++ leBytes 8 index, borshBytes e.1.val),
   (valuesPrefix ++ leBytes 8 index, leBytes 16 e.2)]

def records (s : Map) : List (Bytes × Bytes) :=
  (stateKey, header s.entries.length) ::
    (s.entries.zipIdx.flatMap fun (e, i) => entryRecords i e)

def encode : State → RawStorage
  | none => ∅
  | some m => (records m).toFinset

end Linkdrop.Boundary
