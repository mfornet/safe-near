import NearNode.Primitives.Outcome
import NearNode.Primitives.Storage
import NearNode.Primitives.Transaction
import NearNode.Store.Format
import NearNode.Trie.Update
import NearRuntime.ChangeLog
import NearRuntime.StateEncoding

/-!
# The state changes of a block, with their causes

nearcore keeps the state changes of every block in `DBCol::StateChanges`, keyed by block hash and trie key, one
`RawStateChangesWithTrieKey` (the key and a list of `(cause, new value)`) per trie key that a chunk's commits touched.
`EXPERIMENTAL_changes_in_block` lists the kinds (`StateChangesKinds::from_changes`: one entry per trie key of the account, contract
code, access key and contract data kinds, in key order, whatever the cause) and `EXPERIMENTAL_changes` lists the values with their
causes.

The record of a block and shard here is the Borsh `Vec<RawStateChangesWithTrieKey>` of the exposed kinds, built from the commit log
the runtime returns (`Near.ApplyResult.changes`, and the validator accounts update's), with the native hashes of the transactions
and receipts that are the causes and the bytes of each value as the trie stores it. It is keyed by `block hash ++ ShardUId`, the same
key as `DBCol::TrieChanges`, so garbage collection removes it with the block.
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

/-- The trie key a key of the runtime's change log stands for (`none` for a key family the node does not store). -/
def trieKeyOf? (k : Near.ChangeKey) : Option TrieKey :=
  let handle (pk : Near.PublicKey) : Option PublicKeyHandle :=
    match Codec.decodeAll (α := PublicKey) (ByteArray.mk pk.toArray) with
    | .ok p => keyHandleOf p
    | .error _ => none
  match k with
  | .account id => some (.account ⟨id⟩)
  | .contractCode id => some (.contractCode ⟨id⟩)
  | .accessKey id pk => (handle pk).map fun h => .accessKey ⟨id⟩ h
  | .gasKeyNonce id pk lane => (handle pk).map fun h => .gasKeyNonce ⟨id⟩ h lane.toUInt16
  | .data id key => some (.contractData ⟨id⟩ (ByteArray.mk key.toArray))

private def u64le (n : Nat) : ByteArray :=
  ⟨(List.range 8).toArray.map fun i => UInt8.ofNat (n / 2 ^ (8 * i) % 256)⟩

/-- The value a commit left under a key, as the trie stores it. `catalogue` holds the bytes of the codes by their hash name,
`hashOfLabel` gives the 32 bytes a hash name stands for and `digest` hashes bytes otherwise. -/
def valueBytes (catalogue : List (String × List UInt8)) (hashOfLabel : String → Option (List UInt8))
    (digest : List UInt8 → List UInt8) : Near.ChangeValue → Except String ByteArray
  | .account a => do
    let code ←
      match a.code with
      | none => pure none
      | some c =>
        match Near.Assoc.lookup catalogue c.hash with
        | some bytes => pure (some (bytes, (hashOfLabel c.hash).getD (digest bytes)))
        | none => throw s!"the code {c.hash} of an account is not in the catalogue"
    let v ← Near.StateEncoding.accountValue (code.map (·.1)) a (fun _ => (code.map (·.2)).getD [])
    pure ⟨v.toArray⟩
  | .accessKey k => do pure ⟨(← Near.StateEncoding.accessKey k).toArray⟩
  | .nonce n => pure (u64le n)
  | .code c =>
    match Near.Assoc.lookup catalogue c.hash with
    | some bytes => pure ⟨bytes.toArray⟩
    | none => throw s!"the code {c.hash} is not in the catalogue"
  | .data v => pure ⟨v.toArray⟩

/-- The `StateChangeCause` of a cause of the runtime's log. `txHashes` are the chunk's transactions in order and `native` gives the
native id of a receipt. -/
def causeOf (txHashes : Array ByteArray) (native : Nat → Except String CryptoHash) :
    Near.ChangeCause → Except String StateChangeCause
  | .transaction i =>
    match txHashes[i]? with
    | some h => pure (.transactionProcessing ⟨h⟩)
    | none => throw s!"transaction {i} has no hash"
  | .receiptProcessing id => do pure (.receiptProcessing (← native id))
  | .gasReward id => do pure (.actionReceiptGasReward (← native id))
  | .validatorAccountsUpdate => pure .validatorAccountsUpdate

/-- Group the log by trie key, in the order of the commits, keys sorted as RocksDB would. A change of a key family the node does not
store is dropped. -/
def rawChanges (changes : List Near.StateChange)
    (cause : Near.ChangeCause → Except String StateChangeCause)
    (value : Near.ChangeValue → Except String ByteArray) :
    Except String (Array RawStateChangesWithTrieKey) := do
  let mut index : Std.HashMap ByteArray Nat := {}
  let mut out : Array (ByteArray × RawStateChangesWithTrieKey) := #[]
  for c in changes do
    let some key := trieKeyOf? c.key | continue
    let raw := TrieKey.toVec key
    let data ← c.value.mapM value
    let change : RawStateChange := ⟨← cause c.cause, data⟩
    match index[raw]? with
    | some i =>
      out := out.modify i fun (r, e) => (r, { e with changes := e.changes.push change })
    | none =>
      index := index.insert raw out.size
      out := out.push (raw, ⟨key, #[change]⟩)
  return (out.qsort fun a b => keyLt a.1 b.1).map (·.2)

/-- The entries that differ between the pre-state and the post-state of a chunk (`none` for an entry that is gone) and are of the four
kinds, yet are in none of the records: a fault of the log. The entries of the post-state are authoritative. -/
def missedKeys (diff : Array (ByteArray × Option ByteArray)) (records : Array RawStateChangesWithTrieKey) :
    Array ByteArray :=
  let seen : Std.HashSet ByteArray := records.foldl (fun s r => s.insert (TrieKey.toVec r.trieKey)) {}
  diff.filterMap fun (k, _) => if (kindOfKey? k).isSome && !seen.contains k then some k else none

/-- The record of a block and shard. -/
def stateChangesBytes (changes : Array RawStateChangesWithTrieKey) : ByteArray :=
  Codec.encode changes

def stateChangesOfBytes? (b : ByteArray) : Option (Array RawStateChangesWithTrieKey) :=
  (Codec.decodeAll (α := Array RawStateChangesWithTrieKey) b).toOption

/-- The kind a record lists for its key, `StateChangesKinds::from_changes`. -/
def kindOfTrieKey? : TrieKey → Option (ChangeKind × AccountId)
  | .account a => some (.account, a)
  | .contractCode a => some (.contractCode, a)
  | .accessKey a _ => some (.accessKey, a)
  | .contractData a _ => some (.data, a)
  | _ => none

end Near.Node.Chain
