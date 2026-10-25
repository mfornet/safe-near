import NearNode.Primitives.Storage
import NearNode.Store.Format
import NearNode.Trie.Update

/-!
# The trie keys a block changed, by key kind

nearcore keeps the state changes of every block in `DBCol::StateChanges`, keyed by block hash and trie key, one
`RawStateChangesWithTrieKey` (the key and a list of `(cause, new value)`) per committed key. Two RPC methods read them:
`EXPERIMENTAL_changes_in_block` lists the kinds (`StateChangesKinds::from_changes`: one entry per trie key of the account,
contract code, access key and contract data kinds, in key order, whatever the cause) and `EXPERIMENTAL_changes` lists the
values with their causes.

The Lean runtime returns the post-state of a chunk, not a log of the writes that led to it, so the node keeps what the
post-state determines: the keys whose entry differs between the pre-state and the post-state of the chunk, and whether the
entry is gone. That is enough for the kinds, which carry no value and no cause; it is not enough for
`EXPERIMENTAL_changes` (see the design notes, "F3"), and a key that was written with its old value or restored by a later
write is not seen. One record per block and shard, `block hash ++ ShardUId`, the same key as `DBCol::TrieChanges`, so
garbage collection removes it with the block.
-/

namespace Near.Node.Chain

open Near.Node Near.Node.Borsh

/-- The kinds `StateChangesKinds` reports. -/
inductive ChangeKind where
  | account
  | accessKey
  | data
  | contractCode
  deriving BEq, Inhabited

/-- The kind and the account of a raw trie key, if it is one of the four kinds. -/
def kindOfKey? (raw : ByteArray) : Option (ChangeKind × AccountId) :=
  match TrieKey.parse? raw with
  | some (.account a) => some (.account, a)
  | some (.contractCode a) => some (.contractCode, a)
  | some (.accessKey a _) => some (.accessKey, a)
  | some (.contractData a _) => some (.data, a)
  | _ => none

/-- Lexicographic order of byte strings (the order of the keys of a RocksDB column). -/
def keyLt (a b : ByteArray) : Bool :=
  Id.run do
    for i in [0:min a.size b.size] do
      if a[i]! != b[i]! then
        return a[i]! < b[i]!
    return a.size < b.size

/-- The raw keys among `changes` (the entries that differ, `none` for an entry that is gone) that are of the four kinds,
sorted by key bytes, with whether the entry is gone. -/
def touchedOf (changes : Array (ByteArray × Option ByteArray)) : Array (ByteArray × Bool) :=
  let kept := changes.filterMap fun (k, v) => (kindOfKey? k).map fun _ => (k, v.isNone)
  kept.qsort fun a b => keyLt a.1 b.1

/-- The record of a block and shard. -/
def touchedBytes (touched : Array (ByteArray × Bool)) : ByteArray :=
  Codec.encode touched

def touchedOfBytes? (b : ByteArray) : Option (Array (ByteArray × Bool)) :=
  (Codec.decodeAll (α := Array (ByteArray × Bool)) b).toOption

end Near.Node.Chain
