import NearNode.Primitives.Basic

/-!
# Ordered maps

`BTreeMap` and `HashMap` are a `u32` count and the entries in ascending key order (Borsh sorts a
`HashMap` when it encodes). Decoding accepts any order and keeps the last value of a repeated key.
-/

namespace Near.Node

open Borsh

/-- The entries of a `BTreeMap` or `HashMap`, ascending by key. -/
structure SortedMap (K V : Type) where
  entries : Array (K × V)
  deriving BEq, Inhabited

instance [Ord K] [Codec K] [Codec V] : Codec (SortedMap K V) :=
  .isoOf (α := Array (K × V)) (.btreeMap compare inferInstance inferInstance) .mk SortedMap.entries

/-- Account ids are ordered as their strings. -/
instance : Ord AccountId :=
  ⟨fun a b => compare a.val b.val⟩

/-- Hashes are ordered as their bytes. -/
instance : Ord CryptoHash :=
  ⟨fun a b => compareBytes a.bytes b.bytes⟩

namespace SortedMap

/-- The value of `k`. -/
def find? [BEq K] (m : SortedMap K V) (k : K) : Option V :=
  m.entries.findSome? fun (k', v) => if k' == k then some v else none

end SortedMap

end Near.Node
