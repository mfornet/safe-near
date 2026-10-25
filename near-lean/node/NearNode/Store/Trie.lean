import NearNode.Store.Db
import NearNode.Trie

/-!
# Tries in the store

The `State` column holds the nodes and values of every shard's trie by `ShardUId ++ hash`
(`TrieCachingStorage::get_key_from_shard_uid_and_hash`) with their reference counts. This turns
`TrieChanges` into operations of one commit and reads nodes back through a `NodeSource`.
-/

namespace Near.Node.Store

open Trie

/-- `ShardUId` as it prefixes `State` keys: `version` then `shard_id`, both `u32` little endian. -/
def shardUIdKey (version shardId : UInt32) : ByteArray :=
  le32 (le32 ByteArray.empty version.toNat) shardId.toNat

def stateKey (shard : ByteArray) (h : CryptoHash) : ByteArray :=
  shard ++ h.bytes

/-- The nodes and values of the trie of `shard` in a view of the store. -/
def Tables.nodeSource (t : Tables) (shard : ByteArray) : NodeSource :=
  ⟨fun h => t.get .state (stateKey shard h)⟩

/-- Add the references of `TrieChanges`, with the data of the nodes and values: what nearcore does
when a chunk is applied (`ShardTries::apply_insertions`). -/
def trieInsertOps (shard : ByteArray) (c : TrieChanges) : Array Op :=
  c.insertions.map fun a => Op.rcAdd .state (stateKey shard a.hash) a.data a.rc.toNat

/-- Remove the references: what nearcore does when the block is garbage collected
(`ShardTries::apply_deletions`). The old root is no longer readable afterwards. -/
def trieDeleteOps (shard : ByteArray) (c : TrieChanges) : Array Op :=
  c.deletions.map fun d =>
    Op.rcAdd .state (stateKey shard d.hash) ByteArray.empty (-(d.rc.toNat : Int))

/-- The reference count changes of a chunk's trie as `DBCol::TrieChanges` keeps them for garbage collection: the
insertions (to take back when the block is on a fork) and the deletions (to apply when the block is garbage
collected on the canonical chain), as `u32` count, then hash and `u32` references each, little endian. The data of
the inserted nodes is in the `State` column already. -/
def changesBytes (c : TrieChanges) : ByteArray :=
  let refs (xs : Array (CryptoHash × UInt32)) (d : ByteArray) : ByteArray :=
    xs.foldl (fun d (h, n) => le32 (d ++ h.bytes) n.toNat) (le32 d xs.size)
  refs (c.deletions.map fun x => (x.hash, x.rc))
    (refs (c.insertions.map fun x => (x.hash, x.rc)) ByteArray.empty)

/-- The references of `changesBytes`: insertions and deletions; `none` for bytes that are not that. -/
def changesOfBytes? (b : ByteArray) :
    Option (Array (CryptoHash × Nat) × Array (CryptoHash × Nat)) :=
  let u32 (i : Nat) : Nat :=
    (b.get! i).toNat + (b.get! (i + 1)).toNat * 256 + (b.get! (i + 2)).toNat * 65536 +
      (b.get! (i + 3)).toNat * 16777216
  let refs (i : Nat) : Option (Array (CryptoHash × Nat) × Nat) :=
    if i + 4 > b.size then none
    else
      let n := u32 i
      if i + 4 + 36 * n > b.size then none
      else
        some
          ((Array.range n).map
              (fun k => (⟨b.extract (i + 4 + 36 * k) (i + 36 + 36 * k)⟩, u32 (i + 36 + 36 * k))),
            i + 4 + 36 * n)
  match refs 0 with
  | some (ins, next) =>
    match refs next with
    | some (del, stop) => if stop == b.size then some (ins, del) else none
    | none => none
  | none => none

/-- What garbage collection does for a block on the canonical chain: the references the chunk's update removed
(`ShardTries::apply_deletions`), once the states before it are no longer needed. -/
def deleteOpsOfRefs (shard : ByteArray) (refs : Array (CryptoHash × Nat)) : Array Op :=
  refs.map fun (h, n) => Op.rcAdd .state (stateKey shard h) ByteArray.empty (-(n : Int))

/-- What it does for a block on a fork: the references its update added (`ShardTries::revert_insertions`). -/
def revertOpsOfRefs (shard : ByteArray) (refs : Array (CryptoHash × Nat)) : Array Op :=
  deleteOpsOfRefs shard refs

/-- Both. -/
def trieOps (shard : ByteArray) (c : TrieChanges) : Array Op :=
  trieInsertOps shard c ++ trieDeleteOps shard c

end Near.Node.Store
