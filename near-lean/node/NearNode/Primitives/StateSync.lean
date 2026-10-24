import NearNode.Primitives.Epoch
import NearNode.Primitives.Block

/-!
# State sync

`near-primitives::state_sync`, `state_part` and `network` at `=0.37.4`: the shard state sync
headers and responses (all versions), state parts, the keys and acknowledgements of the state sync
requests, the dump progress, and the peer id and account announcements. A compressed `StatePartV1`
is a zstd frame that stays opaque here.
-/

namespace Near.Node

open Borsh

/-- `StateRootNode`: the serialized root node of a trie and its memory usage. -/
structure StateRootNode where
  data : ByteArray
  memoryUsage : UInt64
  deriving BEq, Inhabited

instance : Codec StateRootNode :=
  .iso (ByteArray × UInt64) (fun (d, m) => ⟨d, m⟩) fun x => (x.data, x.memoryUsage)

/-- `STATE_PART_MEMORY_LIMIT`: 30 MiB. -/
def statePartMemoryLimit : Nat :=
  30 * 1048576

/-- `get_num_state_parts`; `none` where the sum overflows (nearcore is built with overflow checks). -/
def getNumStateParts (memoryUsage : UInt64) : Option UInt64 :=
  let sum := memoryUsage.toNat + statePartMemoryLimit - 1
  if sum < 2 ^ 64 then some (sum / statePartMemoryLimit).toUInt64 else none

/-- `ReceiptProofResponse`: the receipt proofs that arrived in a block. -/
structure ReceiptProofResponse where
  blockHash : CryptoHash
  proofs : Array ReceiptProof
  deriving BEq, Inhabited

instance : Codec ReceiptProofResponse :=
  .iso (CryptoHash × Array ReceiptProof) (fun (b, p) => ⟨b, p⟩) fun x => (x.blockHash, x.proofs)

/-- `RootProof`. -/
structure RootProof where
  root : CryptoHash
  path : Array MerklePathItem
  deriving BEq, Inhabited

instance : Codec RootProof :=
  .iso (CryptoHash × Array MerklePathItem) (fun (r, p) => ⟨r, p⟩) fun x => (x.root, x.path)

/-- `StateHeaderKey`. -/
structure StateHeaderKey where
  shardId : ShardId
  syncHash : CryptoHash
  deriving BEq, Inhabited

instance : Codec StateHeaderKey :=
  .iso (ShardId × CryptoHash) (fun (s, h) => ⟨s, h⟩) fun x => (x.shardId, x.syncHash)

/-- `StatePartKey`. -/
structure StatePartKey where
  syncHash : CryptoHash
  shardId : ShardId
  partId : UInt64
  deriving BEq, Inhabited

instance : Codec StatePartKey :=
  .iso (CryptoHash × ShardId × UInt64) (fun (h, s, p) => ⟨h, s, p⟩) fun x =>
    (x.syncHash, x.shardId, x.partId)

/-- `PartIdOrHeader`. -/
inductive PartIdOrHeader where
  | part (partId : UInt64)
  | header
  deriving BEq, Inhabited

instance : Codec PartIdOrHeader :=
  .enum "PartIdOrHeader"
    [.variant 0 UInt64 .part fun
        | .part p => some p
        | _ => none,
      .const 1 .header]

/-- `StateRequestAckBody`. -/
inductive StateRequestAckBody where
  | willRespond
  | busy
  | error
  deriving BEq, Inhabited

instance : Codec StateRequestAckBody :=
  .enum "StateRequestAckBody" [.const 0 .willRespond, .const 1 .busy, .const 2 .error]

/-- `StateRequestAck`. -/
structure StateRequestAck where
  shardId : ShardId
  syncHash : CryptoHash
  partIdOrHeader : PartIdOrHeader
  body : StateRequestAckBody
  deriving BEq, Inhabited

instance : Codec StateRequestAck :=
  .iso (ShardId × CryptoHash × PartIdOrHeader × StateRequestAckBody)
    (fun (s, h, p, b) => ⟨s, h, p, b⟩) fun x => (x.shardId, x.syncHash, x.partIdOrHeader, x.body)

/-- `ShardStateSyncResponseHeaderV1`. -/
structure ShardStateSyncResponseHeaderV1 where
  chunk : ShardChunkV1
  chunkProof : Array MerklePathItem
  prevChunkHeader : Option ShardChunkHeaderV1
  prevChunkProof : Option (Array MerklePathItem)
  incomingReceiptsProofs : Array ReceiptProofResponse
  rootProofs : Array (Array RootProof)
  stateRootNode : StateRootNode
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseHeaderV1 :=
  .iso
    (ShardChunkV1 ×
      Array MerklePathItem ×
      Option ShardChunkHeaderV1 ×
      Option (Array MerklePathItem) ×
      Array ReceiptProofResponse × Array (Array RootProof) × StateRootNode)
    (fun (c, cp, ph, pp, i, r, s) => ⟨c, cp, ph, pp, i, r, s⟩) fun x =>
    (x.chunk, x.chunkProof, x.prevChunkHeader, x.prevChunkProof, x.incomingReceiptsProofs,
      x.rootProofs, x.stateRootNode)

/-- `ShardStateSyncResponseHeaderV2`: a versioned chunk and chunk header. -/
structure ShardStateSyncResponseHeaderV2 where
  chunk : ShardChunk
  chunkProof : Array MerklePathItem
  prevChunkHeader : Option ShardChunkHeader
  prevChunkProof : Option (Array MerklePathItem)
  incomingReceiptsProofs : Array ReceiptProofResponse
  rootProofs : Array (Array RootProof)
  stateRootNode : StateRootNode
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseHeaderV2 :=
  .iso
    (ShardChunk ×
      Array MerklePathItem ×
      Option ShardChunkHeader ×
      Option (Array MerklePathItem) ×
      Array ReceiptProofResponse × Array (Array RootProof) × StateRootNode)
    (fun (c, cp, ph, pp, i, r, s) => ⟨c, cp, ph, pp, i, r, s⟩) fun x =>
    (x.chunk, x.chunkProof, x.prevChunkHeader, x.prevChunkProof, x.incomingReceiptsProofs,
      x.rootProofs, x.stateRootNode)

/-- `ShardStateSyncResponseHeader`. -/
inductive ShardStateSyncResponseHeader where
  | v1 (h : ShardStateSyncResponseHeaderV1)
  | v2 (h : ShardStateSyncResponseHeaderV2)
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseHeader :=
  .enum "ShardStateSyncResponseHeader"
    [.variant 0 ShardStateSyncResponseHeaderV1 .v1 fun
        | .v1 h => some h
        | _ => none,
      .variant 1 ShardStateSyncResponseHeaderV2 .v2 fun
        | .v2 h => some h
        | _ => none]

namespace ShardStateSyncResponseHeader

/-- `chunk_height_included`. -/
def chunkHeightIncluded : ShardStateSyncResponseHeader → BlockHeight
  | .v1 h => h.chunk.header.heightIncluded
  | .v2 h =>
    match h.chunk with
    | .v1 c => c.header.heightIncluded
    | .v2 c => c.header.heightIncluded

/-- `chunk_prev_state_root`. -/
def chunkPrevStateRoot : ShardStateSyncResponseHeader → CryptoHash
  | .v1 h => h.chunk.header.inner.prevStateRoot
  | .v2 h =>
    match h.chunk with
    | .v1 c => c.header.inner.prevStateRoot
    | .v2 c => c.header.prevStateRoot

/-- `state_root_node`. -/
def stateRootNode : ShardStateSyncResponseHeader → StateRootNode
  | .v1 h => h.stateRootNode
  | .v2 h => h.stateRootNode

/-- `num_state_parts`. -/
def numStateParts (h : ShardStateSyncResponseHeader) : Option UInt64 :=
  getNumStateParts h.stateRootNode.memoryUsage

end ShardStateSyncResponseHeader

/-- `BitArray`: a bitmap and its capacity in bits. -/
structure BitArray where
  data : ByteArray
  capacity : UInt64
  deriving BEq, Inhabited

instance : Codec BitArray :=
  .iso (ByteArray × UInt64) (fun (d, c) => ⟨d, c⟩) fun x => (x.data, x.capacity)

/-- `CachedParts`. -/
inductive CachedParts where
  | allParts
  | noParts
  | bitArray (b : BitArray)
  deriving BEq, Inhabited

instance : Codec CachedParts :=
  .enum "CachedParts"
    [.const 0 .allParts, .const 1 .noParts,
      .variant 2 BitArray .bitArray fun
        | .bitArray b => some b
        | _ => none]

/-- `StatePartV0`: an uncompressed Borsh `PartialState`. -/
structure StatePartV0 where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec StatePartV0 :=
  .iso ByteArray .mk StatePartV0.bytes

/-- `StatePartV1`: a zstd-compressed Borsh `PartialState`. -/
structure StatePartV1 where
  bytesCompressed : ByteArray
  deriving BEq, Inhabited

instance : Codec StatePartV1 :=
  .iso ByteArray .mk StatePartV1.bytesCompressed

/-- `StatePart`. -/
inductive StatePart where
  | v0 (p : StatePartV0)
  | v1 (p : StatePartV1)
  deriving BEq, Inhabited

instance : Codec StatePart :=
  .enum "StatePart"
    [.variant 0 StatePartV0 .v0 fun
        | .v0 p => some p
        | _ => none,
      .variant 1 StatePartV1 .v1 fun
        | .v1 p => some p
        | _ => none]

namespace StatePart

/-- `payload_length`. -/
def payloadLength : StatePart → Nat
  | .v0 p => p.bytes.size
  | .v1 p => p.bytesCompressed.size

/-- `PART_ENTRY_LIMIT`: the most trie values a part may hold. -/
def entryLimit : Nat :=
  2 * statePartMemoryLimit / 50

/-- `StatePart::to_partial_state` for an uncompressed part: the Borsh `PartialState`, if its entry
count is within the limit. A compressed part needs zstd, which is not implemented. -/
def toPartialState? : StatePart → Option PartialState
  | .v0 p =>
    if p.bytes.size < 5 || p.bytes.get! 0 != 0 then none
    else
      match Codec.decodeAll (α := UInt32) (p.bytes.extract 1 5) with
      | .ok n => if n.toNat ≤ entryLimit then (Codec.decodeAll p.bytes).toOption else none
      | .error _ => none
  | .v1 _ => none

end StatePart

/-- `ShardStateSyncResponseV1`. -/
structure ShardStateSyncResponseV1 where
  header : Option ShardStateSyncResponseHeaderV1
  part : Option (UInt64 × ByteArray)
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseV1 :=
  .iso (Option ShardStateSyncResponseHeaderV1 × Option (UInt64 × ByteArray)) (fun (h, p) => ⟨h, p⟩)
    fun x => (x.header, x.part)

/-- `ShardStateSyncResponseV2`. -/
structure ShardStateSyncResponseV2 where
  header : Option ShardStateSyncResponseHeaderV2
  part : Option (UInt64 × ByteArray)
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseV2 :=
  .iso (Option ShardStateSyncResponseHeaderV2 × Option (UInt64 × ByteArray)) (fun (h, p) => ⟨h, p⟩)
    fun x => (x.header, x.part)

/-- `ShardStateSyncResponseV3`. -/
structure ShardStateSyncResponseV3 where
  header : Option ShardStateSyncResponseHeaderV2
  part : Option (UInt64 × ByteArray)
  cachedParts : Option CachedParts
  canGenerate : Bool
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseV3 :=
  .iso
    (Option ShardStateSyncResponseHeaderV2 ×
      Option (UInt64 × ByteArray) × Option CachedParts × Bool)
    (fun (h, p, c, g) => ⟨h, p, c, g⟩) fun x => (x.header, x.part, x.cachedParts, x.canGenerate)

/-- `ShardStateSyncResponseV4`. -/
structure ShardStateSyncResponseV4 where
  header : Option ShardStateSyncResponseHeaderV2
  part : Option (UInt64 × StatePart)
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponseV4 :=
  .iso (Option ShardStateSyncResponseHeaderV2 × Option (UInt64 × StatePart)) (fun (h, p) => ⟨h, p⟩)
    fun x => (x.header, x.part)

/-- `ShardStateSyncResponse`. -/
inductive ShardStateSyncResponse where
  | v1 (r : ShardStateSyncResponseV1)
  | v2 (r : ShardStateSyncResponseV2)
  | v3 (r : ShardStateSyncResponseV3)
  | v4 (r : ShardStateSyncResponseV4)
  deriving BEq, Inhabited

instance : Codec ShardStateSyncResponse :=
  .enum "ShardStateSyncResponse"
    [.variant 0 ShardStateSyncResponseV1 .v1 fun
        | .v1 r => some r
        | _ => none,
      .variant 1 ShardStateSyncResponseV2 .v2 fun
        | .v2 r => some r
        | _ => none,
      .variant 2 ShardStateSyncResponseV3 .v3 fun
        | .v3 r => some r
        | _ => none,
      .variant 3 ShardStateSyncResponseV4 .v4 fun
        | .v4 r => some r
        | _ => none]

namespace ShardStateSyncResponse

/-- `part_id`. -/
def partId : ShardStateSyncResponse → Option UInt64
  | .v1 r => r.part.map (·.1)
  | .v2 r => r.part.map (·.1)
  | .v3 r => r.part.map (·.1)
  | .v4 r => r.part.map (·.1)

/-- `payload_length`. -/
def payloadLength : ShardStateSyncResponse → Option UInt64
  | .v1 r => r.part.map (·.2.size.toUInt64)
  | .v2 r => r.part.map (·.2.size.toUInt64)
  | .v3 r => r.part.map (·.2.size.toUInt64)
  | .v4 r => r.part.map (·.2.payloadLength.toUInt64)

end ShardStateSyncResponse

/-- `StateSyncDumpProgress`. -/
inductive StateSyncDumpProgress where
  | allDumped (epochId : EpochId) (epochHeight : EpochHeight)
  | skipped (epochId : EpochId) (epochHeight : EpochHeight)
  | inProgress (epochId : EpochId) (epochHeight : EpochHeight) (syncHash : CryptoHash)
  deriving BEq, Inhabited

instance : Codec StateSyncDumpProgress :=
  .enum "StateSyncDumpProgress"
    [.variant 0 (EpochId × EpochHeight) (fun (e, h) => .allDumped e h) fun
        | .allDumped e h => some (e, h)
        | _ => none,
      .variant 1 (EpochId × EpochHeight) (fun (e, h) => .skipped e h) fun
        | .skipped e h => some (e, h)
        | _ => none,
      .variant 2 (EpochId × EpochHeight × CryptoHash) (fun (e, h, s) => .inProgress e h s) fun
        | .inProgress e h s => some (e, h, s)
        | _ => none]

/-- `PeerId`: the public key of a node. -/
structure PeerId where
  key : PublicKey
  deriving BEq, Inhabited

instance : Codec PeerId :=
  .iso PublicKey .mk PeerId.key

/-- `AnnounceAccount`: a validator announces the peer that serves its account. -/
structure AnnounceAccount where
  accountId : AccountId
  peerId : PeerId
  epochId : EpochId
  signature : Signature
  deriving BEq, Inhabited

instance : Codec AnnounceAccount :=
  .iso (AccountId × PeerId × EpochId × Signature) (fun (a, p, e, s) => ⟨a, p, e, s⟩) fun x =>
    (x.accountId, x.peerId, x.epochId, x.signature)

/-- `AnnounceAccount::hash`: the hash that the signature covers. -/
def AnnounceAccount.hash (a : AnnounceAccount) : CryptoHash :=
  CryptoHash.hashBorsh (a.accountId, a.peerId, a.epochId)

/-- `GenesisId`: the chain id and the hash of its genesis block. -/
structure GenesisId where
  chainId : String
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec GenesisId :=
  .iso (String × CryptoHash) (fun (c, h) => ⟨c, h⟩) fun x => (x.chainId, x.hash)

end Near.Node
