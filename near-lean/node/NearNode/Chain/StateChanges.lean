import NearNode.Primitives.Outcome
import NearNode.Primitives.Storage
import NearNode.Primitives.Transaction
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

/-- The key handle of an access key in the trie, for the key types the model supports. -/
def keyHandleOf : PublicKey → Option PublicKeyHandle
  | .ed25519 k => some (.ed25519 k)
  | .secp256k1 k => some (.secp256k1 k)
  | .mldsa65 _ => none

/-- The signer and key of a transaction. -/
def transactionSigner (t : SignedTransaction) : AccountId × PublicKey :=
  match t.transaction with
  | .v0 t => (t.signerId, t.publicKey)
  | .v1 t => (t.signerId, t.publicKey)

/-- The writes of a chunk that leave an entry as it was, which nearcore records and a comparison of the entries cannot see
(`TrieUpdate::set` and `remove` record every call, whatever the old value). What the node can tell from the chunk's inputs and
outcomes, each as nearcore does it:

* `update_validator_accounts` (`runtime/runtime/src/lib.rs`): `set_account` for every account of `stake_info` that exists, and
  for the protocol treasury if it is not one of them;
* `verify_and_charge_tx_ephemeral` (`verifier.rs`): `set_access_key` and `set_account` for the signer of every transaction;
* `apply_action_receipt`: `set_account` of the receiver after the actions of a receipt that succeeded and left its account
  in place (a receipt that fails rolls its writes back; the account of a receipt that deleted it is gone);
* `remove_account` (`core/store/src/utils/mod.rs`): removes `Account` and `ContractCode` whether or not the account had code,
  then its access keys and data, which exist and so differ.

What it cannot see: a contract's `storage_write` of the value the key held, or `storage_remove` of a key that is not there, a
key written and then restored by a later write of the same chunk, and an account created and deleted in one chunk. The VM
returns no log of its writes. `pre` and `post` are the entries before and after; the result is the raw keys. -/
def writtenKeys (pre post : Std.HashMap ByteArray ByteArray) (validators : List AccountId)
    (txs : Array SignedTransaction) (receipts : Array ExecutionOutcomeWithId) : Array ByteArray :=
  Id.run do
    let mut keys : Array ByteArray := #[]
    for a in validators do
      let k := TrieKey.toVec (.account a)
      if pre.contains k then
        keys := keys.push k
    for t in txs do
      let (signer, pk) := transactionSigner t
      keys := keys.push (TrieKey.toVec (.account signer))
      if let some h := keyHandleOf pk then
        keys := keys.push (TrieKey.toVec (.accessKey signer h))
    for r in receipts do
      let ok :=
        match r.outcome.status with
        | .successValue _ | .successReceiptId _ => true
        | _ => false
      if ok then
        let k := TrieKey.toVec (.account r.outcome.executorId)
        if pre.contains k && post.contains k then
          keys := keys.push k
    for (k, _) in pre do
      if !post.contains k then
        if let some (.account a) := TrieKey.parse? k then
          keys := keys.push (TrieKey.toVec (.contractCode a))
    return keys

/-- The raw keys among `changes` (the entries that differ, `none` for an entry that is gone) and `written` (the keys the chunk
wrote without changing them) that are of the four kinds, sorted by key bytes, with whether the entry is gone. -/
def touchedOf (changes : Array (ByteArray × Option ByteArray)) (written : Array ByteArray := #[]) :
    Array (ByteArray × Bool) :=
  let kept := changes.filterMap fun (k, v) => (kindOfKey? k).map fun _ => (k, v.isNone)
  let seen : Std.HashSet ByteArray := kept.foldl (fun s (k, _) => s.insert k) {}
  let extra :=
    (written.filter fun k => (kindOfKey? k).isSome).foldl
      (fun (acc : Array (ByteArray × Bool) × Std.HashSet ByteArray) k =>
        if acc.2.contains k then acc else (acc.1.push (k, false), acc.2.insert k))
      (#[], seen)
  (kept ++ extra.1).qsort fun a b => keyLt a.1 b.1

/-- The record of a block and shard. -/
def touchedBytes (touched : Array (ByteArray × Bool)) : ByteArray :=
  Codec.encode touched

def touchedOfBytes? (b : ByteArray) : Option (Array (ByteArray × Bool)) :=
  (Codec.decodeAll (α := Array (ByteArray × Bool)) b).toOption

end Near.Node.Chain
