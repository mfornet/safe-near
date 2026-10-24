import NearNode.Primitives.Receipt
import NearNode.Primitives.Congestion

/-!
# Storage-layer types

`near-primitives` `trie_key`, `state` and `types` at `=0.37.4`: the trie key and its raw bytes
(`TrieKey::to_vec`, and the parser back), value references, the flat state value, and the state
change records kept per block.
-/

namespace Near.Node

open Borsh

/-- `PublicKeyHandle`: the on-trie identifier of an access key. Tag 2 does not exist: a full
ML-DSA-65 key never enters the trie, only the SHA3-256 hash (tag 3). -/
inductive PublicKeyHandle where
  | ed25519 (key : ByteArray)
  | secp256k1 (key : ByteArray)
  | mldsa65 (hash : ByteArray)
  deriving BEq, Inhabited

instance : Codec PublicKeyHandle :=
  .enum "PublicKeyHandle"
    [.variantOf 0 (.fixed 32) .ed25519 fun
        | .ed25519 k => some k
        | _ => none,
      .variantOf 1 (.fixed 64) .secp256k1 fun
        | .secp256k1 k => some k
        | _ => none,
      .variantOf 3 (.fixed 32) .mldsa65 fun
        | .mldsa65 k => some k
        | _ => none]

/-- `GlobalContractCodeIdentifier`. -/
inductive GlobalContractCodeIdentifier where
  | codeHash (h : CryptoHash)
  | accountId (a : AccountId)
  deriving BEq, Inhabited

instance : Codec GlobalContractCodeIdentifier :=
  .enum "GlobalContractCodeIdentifier"
    [.variant 0 CryptoHash .codeHash fun
        | .codeHash h => some h
        | _ => none,
      .variant 1 AccountId .accountId fun
        | .accountId a => some a
        | _ => none]

/-- `TrieKey`: the Borsh tag is the column byte, except `DelayedReceipt` (tag 8, column 7) and
`GasKeyNonce` (tag 21, column 2). -/
inductive TrieKey where
  | account (accountId : AccountId)
  | contractCode (accountId : AccountId)
  | accessKey (accountId : AccountId) (keyHandle : PublicKeyHandle)
  | receivedData (receiverId : AccountId) (dataId : CryptoHash)
  | postponedReceiptId (receiverId : AccountId) (dataId : CryptoHash)
  | pendingDataCount (receiverId : AccountId) (receiptId : CryptoHash)
  | postponedReceipt (receiverId : AccountId) (receiptId : CryptoHash)
  | delayedReceiptIndices
  | delayedReceipt (index : UInt64)
  | contractData (accountId : AccountId) (key : ByteArray)
  | promiseYieldIndices
  | promiseYieldTimeout (index : UInt64)
  | promiseYieldReceipt (receiverId : AccountId) (dataId : CryptoHash)
  | bufferedReceiptIndices
  | bufferedReceipt (receivingShard : ShardId) (index : UInt64)
  | bandwidthSchedulerState
  | bufferedReceiptGroupsQueueData (receivingShard : ShardId)
  | bufferedReceiptGroupsQueueItem (receivingShard : ShardId) (index : UInt64)
  | globalContractCode (identifier : GlobalContractCodeIdentifier)
  | globalContractNonce (identifier : GlobalContractCodeIdentifier)
  | promiseYieldStatus (receiverId : AccountId) (dataId : CryptoHash)
  | yieldIdToDataId (receiverId : AccountId) (yieldId : CryptoHash)
  | dataIdToYieldId (receiverId : AccountId) (dataId : CryptoHash)
  | gasKeyNonce (accountId : AccountId) (keyHandle : PublicKeyHandle) (index : UInt16)
  deriving BEq, Inhabited

open TrieKey in
instance : Codec TrieKey :=
  .enum "TrieKey"
    [.variant 0 AccountId .account fun
        | .account a => some a
        | _ => none,
      .variant 1 AccountId .contractCode fun
        | .contractCode a => some a
        | _ => none,
      .variant 2 (AccountId × PublicKeyHandle) (fun (a, k) => .accessKey a k) fun
        | .accessKey a k => some (a, k)
        | _ => none,
      .variant 3 (AccountId × CryptoHash) (fun (a, d) => .receivedData a d) fun
        | .receivedData a d => some (a, d)
        | _ => none,
      .variant 4 (AccountId × CryptoHash) (fun (a, d) => .postponedReceiptId a d) fun
        | .postponedReceiptId a d => some (a, d)
        | _ => none,
      .variant 5 (AccountId × CryptoHash) (fun (a, d) => .pendingDataCount a d) fun
        | .pendingDataCount a d => some (a, d)
        | _ => none,
      .variant 6 (AccountId × CryptoHash) (fun (a, d) => .postponedReceipt a d) fun
        | .postponedReceipt a d => some (a, d)
        | _ => none,
      .const 7 .delayedReceiptIndices,
      .variant 8 UInt64 .delayedReceipt fun
        | .delayedReceipt i => some i
        | _ => none,
      .variant 9 (AccountId × ByteArray) (fun (a, k) => .contractData a k) fun
        | .contractData a k => some (a, k)
        | _ => none,
      .const 10 .promiseYieldIndices,
      .variant 11 UInt64 .promiseYieldTimeout fun
        | .promiseYieldTimeout i => some i
        | _ => none,
      .variant 12 (AccountId × CryptoHash) (fun (a, d) => .promiseYieldReceipt a d) fun
        | .promiseYieldReceipt a d => some (a, d)
        | _ => none,
      .const 13 .bufferedReceiptIndices,
      .variant 14 (ShardId × UInt64) (fun (s, i) => .bufferedReceipt s i) fun
        | .bufferedReceipt s i => some (s, i)
        | _ => none,
      .const 15 .bandwidthSchedulerState,
      .variant 16 ShardId .bufferedReceiptGroupsQueueData fun
        | .bufferedReceiptGroupsQueueData s => some s
        | _ => none,
      .variant 17 (ShardId × UInt64) (fun (s, i) => .bufferedReceiptGroupsQueueItem s i) fun
        | .bufferedReceiptGroupsQueueItem s i => some (s, i)
        | _ => none,
      .variant 18 GlobalContractCodeIdentifier .globalContractCode fun
        | .globalContractCode i => some i
        | _ => none,
      .variant 19 GlobalContractCodeIdentifier .globalContractNonce fun
        | .globalContractNonce i => some i
        | _ => none,
      .variant 20 (AccountId × CryptoHash) (fun (a, d) => .promiseYieldStatus a d) fun
        | .promiseYieldStatus a d => some (a, d)
        | _ => none,
      .variant 21 (AccountId × PublicKeyHandle × UInt16) (fun (a, k, i) => .gasKeyNonce a k i) fun
        | .gasKeyNonce a k i => some (a, k, i)
        | _ => none,
      .variant 22 (AccountId × CryptoHash) (fun (a, d) => .yieldIdToDataId a d) fun
        | .yieldIdToDataId a d => some (a, d)
        | _ => none,
      .variant 23 (AccountId × CryptoHash) (fun (a, d) => .dataIdToYieldId a d) fun
        | .dataIdToYieldId a d => some (a, d)
        | _ => none]

namespace TrieKey

/-- The column bytes of `trie_key::col`. -/
def colAccount : UInt8 :=
  0

def colContractCode : UInt8 :=
  1

def colAccessKey : UInt8 :=
  2

def colDelayedReceiptOrIndices : UInt8 :=
  7

def colContractData : UInt8 :=
  9

/-- `ACCOUNT_DATA_SEPARATOR`. -/
def separator : UInt8 :=
  0x2c

private def le (x : UInt64) : ByteArray :=
  Codec.encode x

private def withAccount (col : UInt8) (a : AccountId) (sep : UInt8) (rest : ByteArray) :
    ByteArray :=
  ((ByteArray.empty.push col).append a.val.toUTF8 |>.push sep).append rest

/-- `TrieKey::to_vec`: the key of the record in the trie. `none` where nearcore panics: a
receiving shard of a buffered receipt that does not fit a `u16`. -/
def toVec? : TrieKey → Option ByteArray
  | .account a => some ((ByteArray.empty.push 0).append a.val.toUTF8)
  | .contractCode a => some ((ByteArray.empty.push 1).append a.val.toUTF8)
  | .accessKey a k => some (withAccount 2 a 2 (Codec.encode k))
  | .receivedData r d => some (withAccount 3 r separator d.bytes)
  | .postponedReceiptId r d => some (withAccount 4 r separator d.bytes)
  | .pendingDataCount r d => some (withAccount 5 r separator d.bytes)
  | .postponedReceipt r d => some (withAccount 6 r separator d.bytes)
  | .delayedReceiptIndices => some (ByteArray.empty.push 7)
  | .delayedReceipt i => some ((ByteArray.empty.push 7).append (le i))
  | .contractData a k => some (withAccount 9 a separator k)
  | .promiseYieldIndices => some (ByteArray.empty.push 10)
  | .promiseYieldTimeout i => some ((ByteArray.empty.push 11).append (le i))
  | .promiseYieldReceipt r d => some (withAccount 12 r separator d.bytes)
  | .bufferedReceiptIndices => some (ByteArray.empty.push 13)
  | .bufferedReceipt s i =>
    if s.toNat ≤ 65535 then
      some (((ByteArray.empty.push 14).append (Codec.encode s.toUInt16)).append (le i))
    else none
  | .bandwidthSchedulerState => some (ByteArray.empty.push 15)
  | .bufferedReceiptGroupsQueueData s => some ((ByteArray.empty.push 16).append (le s))
  | .bufferedReceiptGroupsQueueItem s i =>
    some (((ByteArray.empty.push 17).append (le s)).append (le i))
  | .globalContractCode i => some ((ByteArray.empty.push 18).append (Codec.encode i))
  | .globalContractNonce i => some ((ByteArray.empty.push 19).append (Codec.encode i))
  | .promiseYieldStatus r d => some (withAccount 20 r separator d.bytes)
  | .yieldIdToDataId r d => some (withAccount 22 r separator d.bytes)
  | .dataIdToYieldId r d => some (withAccount 23 r separator d.bytes)
  | .gasKeyNonce a k i => some ((withAccount 2 a 2 (Codec.encode k)).append (Codec.encode i))

/-- `toVec?`, with the empty key where nearcore panics. -/
def toVec (k : TrieKey) : ByteArray :=
  (toVec? k).getD ByteArray.empty

private def indexOf (b : ByteArray) (x : UInt8) (start : Nat) : Option Nat :=
  let rec go (i : Nat) (fuel : Nat) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 => if i < b.size then (if b[i]! == x then some i else go (i + 1) fuel) else none
  go start (b.size + 1)

private def utf8Account (b : ByteArray) : Option AccountId :=
  (String.fromUTF8? b).bind fun s => if AccountId.isValid s then some ⟨s⟩ else none

/-- An account id, the separator, then `n` bytes exactly. -/
private def accountThen (raw : ByteArray) (sep : UInt8) (n : Option Nat) :
    Option (AccountId × ByteArray) := do
  let i ← indexOf raw sep 1
  let a ← utf8Account (raw.extract 1 i)
  let rest := raw.extract (i + 1) raw.size
  match n with
  | some n =>
    if rest.size == n then
      some (a, rest)
    else
      none
  | none =>
    some (a, rest)

private def hashOnly (b : ByteArray) : CryptoHash :=
  ⟨b⟩

/-- Parse the raw key back to the `TrieKey` that `to_vec` wrote. The column byte alone is not
enough in two places: column 7 is the indices when the key has one byte and a delayed receipt when
it has nine, and column 2 is an access key, or a gas key nonce when two bytes follow the handle. -/
def parse? (raw : ByteArray) : Option TrieKey := do
  if raw.size == 0 then
    none
  let col := raw[0]!
  let u64At (p : Nat) : UInt64 :=
    (Codec.decodeAll (α := UInt64) (raw.extract p (p + 8))).toOption.getD 0
  let withHash (mk : AccountId → CryptoHash → TrieKey) : Option TrieKey := do
    let (a, rest) ← accountThen raw separator (some 32)
    some (mk a (hashOnly rest))
  match col with
  | 0 =>
    (utf8Account (raw.extract 1 raw.size)).map .account
  | 1 =>
    (utf8Account (raw.extract 1 raw.size)).map .contractCode
  | 2 =>
    let (a, rest) ← accountThen raw 2 none
    match Impl.Codec.get (Codec.impl : Impl.Codec PublicKeyHandle) rest 0 with
    | .ok k p =>
      if p == rest.size then
        some (.accessKey a k)
      else if p + 2 == rest.size then
        match Codec.decodeAll (α := UInt16) (rest.extract p rest.size) with
        | .ok i =>
          some (.gasKeyNonce a k i)
        | .error _ =>
          none
      else
        none
    | .err _ =>
      none
  | 3 =>
    withHash .receivedData
  | 4 =>
    withHash .postponedReceiptId
  | 5 =>
    withHash .pendingDataCount
  | 6 =>
    withHash .postponedReceipt
  | 7 =>
    if raw.size == 1 then
      some .delayedReceiptIndices
    else if raw.size == 9 then
      some (.delayedReceipt (u64At 1))
    else
      none
  | 9 =>
    let (a, rest) ← accountThen raw separator none
    some (.contractData a rest)
  | 10 =>
    if raw.size == 1 then
      some .promiseYieldIndices
    else
      none
  | 11 =>
    if raw.size == 9 then
      some (.promiseYieldTimeout (u64At 1))
    else
      none
  | 12 =>
    withHash .promiseYieldReceipt
  | 13 =>
    if raw.size == 1 then
      some .bufferedReceiptIndices
    else
      none
  | 14 =>
    if raw.size == 11 then
      let s := (Codec.decodeAll (α := UInt16) (raw.extract 1 3)).toOption.getD 0
      some (.bufferedReceipt s.toUInt64 (u64At 3))
    else
      none
  | 15 =>
    if raw.size == 1 then
      some .bandwidthSchedulerState
    else
      none
  | 16 =>
    if raw.size == 9 then
      some (.bufferedReceiptGroupsQueueData (u64At 1))
    else
      none
  | 17 =>
    if raw.size == 17 then
      some (.bufferedReceiptGroupsQueueItem (u64At 1) (u64At 9))
    else
      none
  | 18 =>
    (Codec.decodeAll (α := GlobalContractCodeIdentifier) (raw.extract 1 raw.size)).toOption.map
        .globalContractCode
  | 19 =>
    (Codec.decodeAll (α := GlobalContractCodeIdentifier) (raw.extract 1 raw.size)).toOption.map
        .globalContractNonce
  | 20 =>
    withHash .promiseYieldStatus
  | 22 =>
    withHash .yieldIdToDataId
  | 23 =>
    withHash .dataIdToYieldId
  | _ =>
    none

end TrieKey

/-- `ValueRef`: a value's length and hash. -/
structure ValueRef where
  length : UInt32
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec ValueRef :=
  .iso (UInt32 × CryptoHash) (fun (l, h) => ⟨l, h⟩) fun x => (x.length, x.hash)

namespace ValueRef

/-- `ValueRef::new`. -/
def ofValue (v : ByteArray) : ValueRef :=
  ⟨v.size.toUInt32, CryptoHash.hash v⟩

end ValueRef

/-- `FlatStateValue`: a reference, or the value itself when it is small. -/
inductive FlatStateValue where
  | ref (r : ValueRef)
  | inlined (v : ByteArray)
  deriving BEq, Inhabited

instance : Codec FlatStateValue :=
  .enum "FlatStateValue"
    [.variant 0 ValueRef .ref fun
        | .ref r => some r
        | _ => none,
      .variant 1 ByteArray .inlined fun
        | .inlined v => some v
        | _ => none]

namespace FlatStateValue

/-- `INLINE_DISK_VALUE_THRESHOLD`. -/
def inlineThreshold : Nat :=
  4000

/-- `FlatStateValue::on_disk`. -/
def onDisk (v : ByteArray) : FlatStateValue :=
  if v.size ≤ inlineThreshold then .inlined v else .ref (ValueRef.ofValue v)

/-- `FlatStateValue::to_value_ref`. -/
def toValueRef : FlatStateValue → ValueRef
  | .ref r => r
  | .inlined v => ValueRef.ofValue v

end FlatStateValue

/-- `StateChangeCause`. -/
inductive StateChangeCause where
  | notWritableToDisk
  | initialState
  | transactionProcessing (txHash : CryptoHash)
  | actionReceiptProcessingStarted (receiptHash : CryptoHash)
  | actionReceiptGasReward (receiptHash : CryptoHash)
  | receiptProcessing (receiptHash : CryptoHash)
  | postponedReceipt (receiptHash : CryptoHash)
  | updatedDelayedReceipts
  | validatorAccountsUpdate
  | migration
  | unusedReshardingV2
  | bandwidthSchedulerStateUpdate
  deriving BEq, Inhabited

open StateChangeCause in
instance : Codec StateChangeCause :=
  .enum "StateChangeCause"
    [.const 0 .notWritableToDisk, .const 1 .initialState,
      .variant 2 CryptoHash .transactionProcessing fun
        | .transactionProcessing h => some h
        | _ => none,
      .variant 3 CryptoHash .actionReceiptProcessingStarted fun
        | .actionReceiptProcessingStarted h => some h
        | _ => none,
      .variant 4 CryptoHash .actionReceiptGasReward fun
        | .actionReceiptGasReward h => some h
        | _ => none,
      .variant 5 CryptoHash .receiptProcessing fun
        | .receiptProcessing h => some h
        | _ => none,
      .variant 6 CryptoHash .postponedReceipt fun
        | .postponedReceipt h => some h
        | _ => none,
      .const 7 .updatedDelayedReceipts, .const 8 .validatorAccountsUpdate, .const 9 .migration,
      .const 10 .unusedReshardingV2, .const 11 .bandwidthSchedulerStateUpdate]

/-- `RawStateChange`: one committed change with its cause; `none` is a deletion. -/
structure RawStateChange where
  cause : StateChangeCause
  data : Option ByteArray
  deriving BEq, Inhabited

instance : Codec RawStateChange :=
  .iso (StateChangeCause × Option ByteArray) (fun (c, d) => ⟨c, d⟩) fun x => (x.cause, x.data)

/-- `RawStateChangesWithTrieKey`. -/
structure RawStateChangesWithTrieKey where
  trieKey : TrieKey
  changes : Array RawStateChange
  deriving BEq, Inhabited

instance : Codec RawStateChangesWithTrieKey :=
  .iso (TrieKey × Array RawStateChange) (fun (k, c) => ⟨k, c⟩) fun x => (x.trieKey, x.changes)

/-- `StateChangesForShard`: a row of the `StateChanges` column. -/
structure StateChangesForShard where
  shardId : ShardId
  stateChanges : Array RawStateChangesWithTrieKey
  deriving BEq, Inhabited

instance : Codec StateChangesForShard :=
  .iso (ShardId × Array RawStateChangesWithTrieKey) (fun (s, c) => ⟨s, c⟩) fun x =>
    (x.shardId, x.stateChanges)

/-- `StateChangesForBlock`. -/
structure StateChangesForBlock where
  blockHash : CryptoHash
  stateChanges : Array StateChangesForShard
  deriving BEq, Inhabited

instance : Codec StateChangesForBlock :=
  .iso (CryptoHash × Array StateChangesForShard) (fun (h, c) => ⟨h, c⟩) fun x =>
    (x.blockHash, x.stateChanges)

/-- `StateChangesForBlockRange`. -/
structure StateChangesForBlockRange where
  blocks : Array StateChangesForBlock
  deriving BEq, Inhabited

instance : Codec StateChangesForBlockRange :=
  .iso (Array StateChangesForBlock) .mk StateChangesForBlockRange.blocks

end Near.Node
