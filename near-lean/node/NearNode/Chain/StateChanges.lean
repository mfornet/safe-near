import NearNode.Primitives.Outcome
import NearNode.Primitives.Storage
import NearNode.Primitives.Transaction
import NearNode.Store.Format
import NearNode.Trie.Update
import NearRuntime.ChangeLog

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

/-- The key handle of an access key in the trie, for the key types the model supports. -/
def keyHandleOf : PublicKey → Option PublicKeyHandle
  | .ed25519 k => some (.ed25519 k)
  | .secp256k1 k => some (.secp256k1 k)
  | .mldsa65 _ => none

/-- The trie key a key of the runtime's change log stands for (`none` for a key family the node does not
store, such as an ML-DSA key). -/
def rawKeyOf? (k : Near.ChangeKey) : Option ByteArray :=
  let handle (pk : Near.PublicKey) : Option PublicKeyHandle :=
    match Codec.decodeAll (α := PublicKey) (ByteArray.mk pk.toArray) with
    | .ok p => keyHandleOf p
    | .error _ => none
  match k with
  | .account id => some (TrieKey.toVec (.account ⟨id⟩))
  | .contractCode id => some (TrieKey.toVec (.contractCode ⟨id⟩))
  | .accessKey id pk => (handle pk).map fun h => TrieKey.toVec (.accessKey ⟨id⟩ h)
  | .gasKeyNonce id pk lane => (handle pk).map fun h => TrieKey.toVec (.gasKeyNonce ⟨id⟩ h lane.toUInt16)
  | .data id key => some (TrieKey.toVec (.contractData ⟨id⟩ (ByteArray.mk key.toArray)))

/-- The keys of the four kinds that a chunk's change log lists (`Near.ApplyResult.changes`, and the validator accounts
update's), each once, with whether its last value is a removal. The log is what the runtime did, commit by commit: it
lists a write of the value the key held and a removal of a key that is not there, which a comparison of the entries
before and after cannot see. -/
def logKeys (changes : List Near.StateChange) : Array (ByteArray × Bool) :=
  let last : Std.HashMap ByteArray Bool :=
    changes.foldl
      (fun m c =>
        match rawKeyOf? c.key with
        | some k => m.insert k c.value.isNone
        | none => m)
      {}
  last.toArray.filter fun (k, _) => (kindOfKey? k).isSome

/-- The raw keys among `changes` (the entries that differ, `none` for an entry that is gone) and the keys of the
chunk's change log that are of the four kinds, sorted by key bytes, with whether the entry is gone, and the entries that
differ without being in the log (a fault of the log: the entries of the post-state are authoritative, so such a key is
listed all the same). -/
def touchedOf (changes : Array (ByteArray × Option ByteArray)) (logged : Array (ByteArray × Bool)) :
    Array (ByteArray × Bool) × Array ByteArray :=
  let seen : Std.HashSet ByteArray := logged.foldl (fun s (k, _) => s.insert k) {}
  let missed :=
    changes.filterMap fun (k, v) =>
      if (kindOfKey? k).isSome && !seen.contains k then some (k, v.isNone) else none
  ((logged ++ missed).qsort fun a b => keyLt a.1 b.1, missed.map (·.1))

/-- The record of a block and shard. -/
def touchedBytes (touched : Array (ByteArray × Bool)) : ByteArray :=
  Codec.encode touched

def touchedOfBytes? (b : ByteArray) : Option (Array (ByteArray × Bool)) :=
  (Codec.decodeAll (α := Array (ByteArray × Bool)) b).toOption

end Near.Node.Chain
