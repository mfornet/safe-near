import NearNode.Primitives.Action

/-!
# Receipts

`near-primitives::receipt` at `=0.37.4`: `Receipt` (only V0 exists, written
without a tag), `ReceiptEnum` with its seven variants, the global contract
distribution receipts, and the state-stored forms.
-/

namespace Near.Node

open Borsh

/-- `DataReceiver`. -/
structure DataReceiver where
  dataId : CryptoHash
  receiverId : AccountId
  deriving BEq, Inhabited

instance : Codec DataReceiver :=
  .iso (CryptoHash × AccountId) (fun (d, r) => ⟨d, r⟩) fun x => (x.dataId, x.receiverId)

/-- `ActionReceipt`. -/
structure ActionReceipt where
  signerId : AccountId
  signerPublicKey : PublicKey
  gasPrice : Balance
  outputDataReceivers : Array DataReceiver
  inputDataIds : Array CryptoHash
  actions : Array Action
  deriving BEq, Inhabited

instance : Codec ActionReceipt :=
  .iso (AccountId × PublicKey × Balance × Array DataReceiver × Array CryptoHash × Array Action)
    (fun (s, k, g, o, i, a) => ⟨s, k, g, o, i, a⟩) fun x =>
    (x.signerId, x.signerPublicKey, x.gasPrice, x.outputDataReceivers, x.inputDataIds, x.actions)

/-- `ActionReceiptV2`: `ActionReceipt` with `refund_to`. -/
structure ActionReceiptV2 where
  signerId : AccountId
  refundTo : Option AccountId
  signerPublicKey : PublicKey
  gasPrice : Balance
  outputDataReceivers : Array DataReceiver
  inputDataIds : Array CryptoHash
  actions : Array Action
  deriving BEq, Inhabited

instance : Codec ActionReceiptV2 :=
  .iso
    (AccountId ×
      Option AccountId × PublicKey × Balance × Array DataReceiver × Array CryptoHash × Array Action)
    (fun (s, f, k, g, o, i, a) => ⟨s, f, k, g, o, i, a⟩) fun x =>
    (x.signerId, x.refundTo, x.signerPublicKey, x.gasPrice, x.outputDataReceivers, x.inputDataIds,
      x.actions)

/-- `DataReceipt`. -/
structure DataReceipt where
  dataId : CryptoHash
  data : Option ByteArray
  deriving BEq, Inhabited

instance : Codec DataReceipt :=
  .iso (CryptoHash × Option ByteArray) (fun (d, v) => ⟨d, v⟩) fun x => (x.dataId, x.data)

/-- `GlobalContractDistributionReceiptV1`. -/
structure GlobalContractDistributionReceiptV1 where
  id : GlobalContractIdentifier
  targetShard : ShardId
  alreadyDeliveredShards : Array ShardId
  code : ByteArray
  deriving BEq, Inhabited

instance : Codec GlobalContractDistributionReceiptV1 :=
  .iso (GlobalContractIdentifier × ShardId × Array ShardId × ByteArray)
    (fun (i, t, a, c) => ⟨i, t, a, c⟩) fun x =>
    (x.id, x.targetShard, x.alreadyDeliveredShards, x.code)

/-- `GlobalContractDistributionReceiptV2`: V1 with a nonce. -/
structure GlobalContractDistributionReceiptV2 where
  id : GlobalContractIdentifier
  targetShard : ShardId
  alreadyDeliveredShards : Array ShardId
  code : ByteArray
  nonce : UInt64
  deriving BEq, Inhabited

instance : Codec GlobalContractDistributionReceiptV2 :=
  .iso (GlobalContractIdentifier × ShardId × Array ShardId × ByteArray × UInt64)
    (fun (i, t, a, c, n) => ⟨i, t, a, c, n⟩) fun x =>
    (x.id, x.targetShard, x.alreadyDeliveredShards, x.code, x.nonce)

/-- `GlobalContractDistributionReceipt`. -/
inductive GlobalContractDistributionReceipt where
  | v1 (r : GlobalContractDistributionReceiptV1)
  | v2 (r : GlobalContractDistributionReceiptV2)
  deriving BEq, Inhabited

instance : Codec GlobalContractDistributionReceipt :=
  .enum "GlobalContractDistributionReceipt"
    [.variant 0 GlobalContractDistributionReceiptV1 .v1 fun
        | .v1 r => some r
        | _ => none,
      .variant 1 GlobalContractDistributionReceiptV2 .v2 fun
        | .v2 r => some r
        | _ => none]

/-- `ReceiptEnum`. -/
inductive ReceiptEnum where
  | action (r : ActionReceipt)
  | data (r : DataReceipt)
  | promiseYield (r : ActionReceipt)
  | promiseResume (r : DataReceipt)
  | globalContractDistribution (r : GlobalContractDistributionReceipt)
  | actionV2 (r : ActionReceiptV2)
  | promiseYieldV2 (r : ActionReceiptV2)
  deriving BEq, Inhabited

instance : Codec ReceiptEnum :=
  .enum "ReceiptEnum"
    [.variant 0 ActionReceipt .action fun
        | .action r => some r
        | _ => none,
      .variant 1 DataReceipt .data fun
        | .data r => some r
        | _ => none,
      .variant 2 ActionReceipt .promiseYield fun
        | .promiseYield r => some r
        | _ => none,
      .variant 3 DataReceipt .promiseResume fun
        | .promiseResume r => some r
        | _ => none,
      .variant 4 GlobalContractDistributionReceipt .globalContractDistribution fun
        | .globalContractDistribution r => some r
        | _ => none,
      .variant 5 ActionReceiptV2 .actionV2 fun
        | .actionV2 r => some r
        | _ => none,
      .variant 6 ActionReceiptV2 .promiseYieldV2 fun
        | .promiseYieldV2 r => some r
        | _ => none]

/-- `ReceiptV0`. -/
structure ReceiptV0 where
  predecessorId : AccountId
  receiverId : AccountId
  receiptId : CryptoHash
  receipt : ReceiptEnum
  deriving BEq, Inhabited

instance : Codec ReceiptV0 :=
  .iso (AccountId × AccountId × CryptoHash × ReceiptEnum) (fun (p, r, i, e) => ⟨p, r, i, e⟩)
    fun x => (x.predecessorId, x.receiverId, x.receiptId, x.receipt)

/-- `Receipt`: only V0 exists, and it is encoded without a tag. -/
inductive Receipt where
  | v0 (r : ReceiptV0)
  deriving BEq, Inhabited

instance : Codec Receipt :=
  .iso ReceiptV0 .v0 fun
    | .v0 r => r

/-- `StateStoredReceiptMetadata`. -/
structure StateStoredReceiptMetadata where
  congestionGas : Gas
  congestionSize : UInt64
  deriving BEq, Inhabited

instance : Codec StateStoredReceiptMetadata :=
  .iso (Gas × UInt64) (fun (g, s) => ⟨g, s⟩) fun x => (x.congestionGas, x.congestionSize)

/-- `StateStoredReceipt`: the bytes `ff ff`, a version, the receipt and its metadata. -/
inductive StateStoredReceipt where
  | v0 (receipt : Receipt) (metadata : StateStoredReceiptMetadata)
  | v1 (receipt : Receipt) (metadata : StateStoredReceiptMetadata)
  deriving BEq, Inhabited

@[instance_reducible]
private def stateStoredMagic : Codec Unit :=
  .tryIsoOf (α := UInt16) inferInstance
    (fun v => if v == 0xFFFF then .ok () else .error (.invalid "StateStoredReceipt tag")) fun _ =>
    (0xFFFF : UInt16)

instance : Codec StateStoredReceipt :=
  .isoOf
    (.pair stateStoredMagic
      (.enum "StateStoredReceipt"
        [.variant 0 (Receipt × StateStoredReceiptMetadata) (fun (r, m) => .v0 r m) fun
            | .v0 r m => some (r, m)
            | _ => none,
          .variant 1 (Receipt × StateStoredReceiptMetadata) (fun (r, m) => .v1 r m) fun
            | .v1 r m => some (r, m)
            | _ => none]))
    (·.2) ((), ·)

/-- `ReceiptOrStateStoredReceipt`: the state-stored form is recognised by its first two bytes. -/
inductive ReceiptOrStateStoredReceipt where
  | receipt (r : Receipt)
  | stateStored (r : StateStoredReceipt)
  deriving BEq, Inhabited

instance : Codec ReceiptOrStateStoredReceipt :=
  let cr : Codec Receipt := inferInstance
  let cs : Codec StateStoredReceipt := inferInstance
  { spec :=
      { enc := fun
          | .receipt r => cr.spec.enc r
          | .stateStored r => cs.spec.enc r
        dec := fun l =>
          match l with
          | u1 :: u2 :: _ =>
            if u1 == 0xFF && u2 == 0xFF then do
              let (r, rest) ← cs.spec.dec l
              pure (.stateStored r, rest)
            else do
              let (r, rest) ← cr.spec.dec l
              pure (.receipt r, rest)
          | _ => throw .eof }
    impl :=
      { put := fun
          | .receipt r, d => cr.impl.put r d
          | .stateStored r, d => cs.impl.put r d
        get := fun d p =>
          if p + 2 ≤ d.size then
            if d[p]! == 0xFF && d[p + 1]! == 0xFF then (cs.impl.get d p).map .stateStored
            else (cr.impl.get d p).map .receipt
          else .err .eof } }

/-- `ReceivedData`. -/
structure ReceivedData where
  data : Option ByteArray
  deriving BEq, Inhabited

instance : Codec ReceivedData :=
  .iso (Option ByteArray) .mk ReceivedData.data

/-- `DelayedReceiptIndices`, `PromiseYieldIndices` and `TrieQueueIndices`. -/
structure TrieQueueIndices where
  firstIndex : UInt64
  nextAvailableIndex : UInt64
  deriving BEq, Inhabited

instance : Codec TrieQueueIndices :=
  .iso (UInt64 × UInt64) (fun (f, n) => ⟨f, n⟩) fun x => (x.firstIndex, x.nextAvailableIndex)

/-- `DelayedReceiptIndices`: same layout as `TrieQueueIndices`. -/
abbrev DelayedReceiptIndices :=
  TrieQueueIndices

/-- `PromiseYieldIndices`: same layout as `TrieQueueIndices`. -/
abbrev PromiseYieldIndices :=
  TrieQueueIndices

/-- `BufferedReceiptIndices`: a `BTreeMap<ShardId, TrieQueueIndices>` as ordered entries. -/
structure BufferedReceiptIndices where
  shardBuffers : Array (ShardId × TrieQueueIndices)
  deriving BEq, Inhabited

instance : Codec BufferedReceiptIndices :=
  .isoOf (α := Array (ShardId × TrieQueueIndices)) (.btreeMap compare inferInstance inferInstance)
    .mk BufferedReceiptIndices.shardBuffers

/-- `PromiseYieldTimeout`. -/
structure PromiseYieldTimeout where
  accountId : AccountId
  dataId : CryptoHash
  expiresAt : BlockHeight
  deriving BEq, Inhabited

instance : Codec PromiseYieldTimeout :=
  .iso (AccountId × CryptoHash × BlockHeight) (fun (a, d, e) => ⟨a, d, e⟩) fun x =>
    (x.accountId, x.dataId, x.expiresAt)

end Near.Node
