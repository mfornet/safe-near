import NearNode.Primitives.Errors
import NearNode.Primitives.Transaction

/-!
# Execution outcomes

`near-primitives::transaction` (`ExecutionOutcome` and friends),
`profile_data_v2`, `profile_data_v3` and `merkle` at `=0.37.4`. The in-memory
`compute_usage` of an outcome is not serialized and has no field here.
-/

namespace Near.Node

open Borsh

/-- Resize to exactly `n` entries: extra values are dropped and missing ones are zero, like the
profile decoders. -/
def fitProfile (n : Nat) (a : Array UInt64) : Array UInt64 :=
  (a.extract 0 n) ++ Array.replicate (n - a.size) 0

/-- `ProfileDataV2`: 72 gas counters (legacy costs, then host function costs). -/
structure ProfileDataV2 where
  data : Array UInt64
  deriving BEq, Inhabited

instance : Codec ProfileDataV2 :=
  .iso (Array UInt64) (fun a => ⟨fitProfile 72 a⟩) fun x => fitProfile 72 x.data

/-- `ProfileDataV3`: 26 action costs, 88 host function costs and the Wasm gas. -/
structure ProfileDataV3 where
  actionsProfile : Array UInt64
  wasmExtProfile : Array UInt64
  wasmGas : Gas
  deriving BEq, Inhabited

instance : Codec ProfileDataV3 :=
  .iso (Array UInt64 × Array UInt64 × Gas) (fun (a, e, g) => ⟨fitProfile 26 a, fitProfile 88 e, g⟩)
    fun x => (fitProfile 26 x.actionsProfile, fitProfile 88 x.wasmExtProfile, x.wasmGas)

/-- `ExecutionMetadataV4`. -/
structure ExecutionMetadataV4 where
  profile : ProfileDataV3
  contracts : Array AccountContract
  deriving BEq, Inhabited

instance : Codec ExecutionMetadataV4 :=
  .iso (ProfileDataV3 × Array AccountContract) (fun (p, c) => ⟨p, c⟩) fun x =>
    (x.profile, x.contracts)

/-- `ExecutionMetadata`. -/
inductive ExecutionMetadata where
  | v1
  | v2 (p : ProfileDataV2)
  | v3 (p : ProfileDataV3)
  | v4 (m : ExecutionMetadataV4)
  deriving BEq, Inhabited

instance : Codec ExecutionMetadata :=
  .enum "ExecutionMetadata"
    [.const 0 .v1,
      .variant 1 ProfileDataV2 .v2 fun
        | .v2 p => some p
        | _ => none,
      .variant 2 ProfileDataV3 .v3 fun
        | .v3 p => some p
        | _ => none,
      .variant 3 ExecutionMetadataV4 .v4 fun
        | .v4 m => some m
        | _ => none]

/-- `ExecutionStatus`. -/
inductive ExecutionStatus where
  | unknown
  | failure (e : TxExecutionError)
  | successValue (value : ByteArray)
  | successReceiptId (id : CryptoHash)
  deriving BEq, Inhabited

instance : Codec ExecutionStatus :=
  .enum "ExecutionStatus"
    [.const 0 .unknown,
      .variant 1 TxExecutionError .failure fun
        | .failure e => some e
        | _ => none,
      .variant 2 ByteArray .successValue fun
        | .successValue v => some v
        | _ => none,
      .variant 3 CryptoHash .successReceiptId fun
        | .successReceiptId i => some i
        | _ => none]

/-- `PartialExecutionStatus`: `ExecutionStatus` without failure details. -/
inductive PartialExecutionStatus where
  | unknown
  | failure
  | successValue (value : ByteArray)
  | successReceiptId (id : CryptoHash)
  deriving BEq, Inhabited

instance : Codec PartialExecutionStatus :=
  .enum "PartialExecutionStatus"
    [.const 0 .unknown, .const 1 .failure,
      .variant 2 ByteArray .successValue fun
        | .successValue v => some v
        | _ => none,
      .variant 3 CryptoHash .successReceiptId fun
        | .successReceiptId i => some i
        | _ => none]

/-- `PartialExecutionOutcome`: the part of an outcome that is hashed into proofs. -/
structure PartialExecutionOutcome where
  receiptIds : Array CryptoHash
  gasBurnt : Gas
  tokensBurnt : Balance
  executorId : AccountId
  status : PartialExecutionStatus
  deriving BEq, Inhabited

instance : Codec PartialExecutionOutcome :=
  .iso (Array CryptoHash × Gas × Balance × AccountId × PartialExecutionStatus)
    (fun (r, g, t, e, s) => ⟨r, g, t, e, s⟩) fun x =>
    (x.receiptIds, x.gasBurnt, x.tokensBurnt, x.executorId, x.status)

/-- `ExecutionOutcome`. -/
structure ExecutionOutcome where
  logs : Array String
  receiptIds : Array CryptoHash
  gasBurnt : Gas
  tokensBurnt : Balance
  executorId : AccountId
  status : ExecutionStatus
  metadata : ExecutionMetadata
  deriving BEq, Inhabited

instance : Codec ExecutionOutcome :=
  .iso
    (Array String ×
      Array CryptoHash × Gas × Balance × AccountId × ExecutionStatus × ExecutionMetadata)
    (fun (l, r, g, t, e, s, m) => ⟨l, r, g, t, e, s, m⟩) fun x =>
    (x.logs, x.receiptIds, x.gasBurnt, x.tokensBurnt, x.executorId, x.status, x.metadata)

/-- The status without failure details. -/
def ExecutionStatus.toPartial : ExecutionStatus → PartialExecutionStatus
  | .unknown => .unknown
  | .failure _ => .failure
  | .successValue v => .successValue v
  | .successReceiptId i => .successReceiptId i

/-- `PartialExecutionOutcome::from(&ExecutionOutcome)`. -/
def ExecutionOutcome.toPartial (o : ExecutionOutcome) : PartialExecutionOutcome :=
  ⟨o.receiptIds, o.gasBurnt, o.tokensBurnt, o.executorId, o.status.toPartial⟩

/-- `ExecutionOutcomeWithId`: the transaction hash or receipt id, then the outcome. -/
structure ExecutionOutcomeWithId where
  id : CryptoHash
  outcome : ExecutionOutcome
  deriving BEq, Inhabited

instance : Codec ExecutionOutcomeWithId :=
  .iso (CryptoHash × ExecutionOutcome) (fun (i, o) => ⟨i, o⟩) fun x => (x.id, x.outcome)

/-- `ExecutionOutcomeWithId::to_hashes`: the id, the hash of the partial outcome and the hash of
each log. -/
def ExecutionOutcomeWithId.toHashes (o : ExecutionOutcomeWithId) : Array CryptoHash :=
  #[o.id, CryptoHash.hashBorsh o.outcome.toPartial] ++
    o.outcome.logs.map fun log => CryptoHash.hash log.toUTF8

/-- The leaf of the chunk outcome tree: the hash of the Borsh encoding of `toHashes`. -/
def ExecutionOutcomeWithId.leafHash (o : ExecutionOutcomeWithId) : CryptoHash :=
  CryptoHash.hashBorsh o.toHashes

/-- `merkle::Direction`. -/
inductive Direction where
  | left
  | right
  deriving BEq, Inhabited

instance : Codec Direction :=
  .enum "Direction" [.const 0 .left, .const 1 .right]

/-- `MerklePathItem`. -/
structure MerklePathItem where
  hash : CryptoHash
  direction : Direction
  deriving BEq, Inhabited

instance : Codec MerklePathItem :=
  .iso (CryptoHash × Direction) (fun (h, d) => ⟨h, d⟩) fun x => (x.hash, x.direction)

/-- `ExecutionOutcomeWithIdAndProof`. -/
structure ExecutionOutcomeWithIdAndProof where
  proof : Array MerklePathItem
  blockHash : CryptoHash
  outcomeWithId : ExecutionOutcomeWithId
  deriving BEq, Inhabited

instance : Codec ExecutionOutcomeWithIdAndProof :=
  .iso (Array MerklePathItem × CryptoHash × ExecutionOutcomeWithId) (fun (p, b, o) => ⟨p, b, o⟩)
    fun x => (x.proof, x.blockHash, x.outcomeWithId)

/-- `ExecutionOutcomeWithProof`: the compact form used in storage. -/
structure ExecutionOutcomeWithProof where
  proof : Array MerklePathItem
  outcome : ExecutionOutcome
  deriving BEq, Inhabited

instance : Codec ExecutionOutcomeWithProof :=
  .iso (Array MerklePathItem × ExecutionOutcome) (fun (p, o) => ⟨p, o⟩) fun x =>
    (x.proof, x.outcome)

end Near.Node
