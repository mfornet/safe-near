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

/-- Both. -/
def trieOps (shard : ByteArray) (c : TrieChanges) : Array Op :=
  trieInsertOps shard c ++ trieDeleteOps shard c

end Near.Node.Store
