import NearNode.Chain.Apply

/-!
# The genesis state

`GenesisStateApplier::apply` (`core/store/src/genesis/state_applier.rs`) for a genesis that holds
accounts and full access keys: the storage usage of every account is recomputed from its records
(`StorageComputer`), and each shard gets the records of the accounts it holds.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh Near.Node.Trie

/-- An account record of the genesis. -/
structure GenesisAccount where
  id : AccountId
  amount : Nat
  locked : Nat
  deriving Inhabited

/-- A full access key record of the genesis. -/
structure GenesisKey where
  id : AccountId
  publicKey : PublicKey
  nonce : Nat
  deriving Inhabited

/-- `StorageUsageConfig` of protocol 86: `num_bytes_account` and `num_extra_bytes_record`. -/
def numBytesAccount : Nat :=
  100

def numExtraBytesRecord : Nat :=
  40

/-- The entries of one shard of the genesis state. -/
def genesisEntries (layout : ShardLayout) (shard : ShardId) (accounts : Array GenesisAccount)
    (keys : Array GenesisKey) : Except String (Array (ByteArray × ByteArray)) := do
  let mine (a : AccountId) : Bool := layout.accountIdToShardId a == some shard
  let usage (a : AccountId) : Nat :=
    keys.foldl
      (fun n k =>
        if k.id == a then
          n + numExtraBytesRecord + (Codec.encode k.publicKey).size +
            (Codec.encode (AccessKey.mk k.nonce.toUInt64 .fullAccess)).size
        else n)
      numBytesAccount
  let state : Near.ChainState :=
    {
      accounts :=
        (accounts.filter (mine ·.id)).toList.map fun a =>
          (a.id.val, { amount := a.amount, locked := a.locked, storageUsage := usage a.id }),
      accessKeys :=
        (keys.filter (mine ·.id)).toList.map fun k =>
          ((k.id.val, (Codec.encode k.publicKey).toList),
            { nonce := k.nonce, permission := .fullAccess }) }
  let entries ← Near.QueueEncoding.encode state [] {} none
  pure (entries.toArray.map fun (k, v) => (⟨k.toArray⟩, ⟨v.toArray⟩))

/-- The tries of the genesis state, one per shard: the roots and the operations that store the nodes. -/
def genesisTries (layout : ShardLayout) (accounts : Array GenesisAccount)
    (keys : Array GenesisKey) : Except String (Std.HashMap UInt64 CryptoHash × Array Store.Op) := do
  let mut roots : Std.HashMap UInt64 CryptoHash := {}
  let mut ops : Array Store.Op := #[]
  for shard in layout.shardIds do
    let entries ← genesisEntries layout shard accounts keys
    let changes ← fromEntries entries
    roots := roots.insert shard changes.newRoot
    ops := ops ++ Store.trieInsertOps (shardKey layout shard) changes
  return (roots, ops)

end Near.Node.Apply
