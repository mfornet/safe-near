import NearNode.Primitives.Block
import NearNode.Primitives.Spice

/-!
# Stateless validation

`near-primitives::stateless_validation` at `=0.37.4`: chunk endorsements, chunk state witnesses
(with the partial state they carry), partial encoded witnesses, the contract-distribution
messages and the data stored per chunk. Every signed message is a struct `inner` plus a signature
over the Borsh bytes of `inner`; `signingBytes` returns them. `usize` fields are `u64` on the
wire and `Box<[u8]>` and `Arc<[u8]>` are `Vec<u8>`. The compressed payloads (`EncodedChunkStateWitness`,
`CompressedContractCode`) are zstd frames that stay opaque here.
-/

namespace Near.Node

open Borsh

/-- Order of `CryptoHash` keys, as `Ord` of the byte array. -/
def compareHash (a b : CryptoHash) : Ordering :=
  compareBytes a.bytes b.bytes

/-- `ChunkProductionKey`: identifies the production of one chunk. -/
structure ChunkProductionKey where
  shardId : ShardId
  epochId : EpochId
  heightCreated : BlockHeight
  deriving BEq, Inhabited

instance : Codec ChunkProductionKey :=
  .iso (ShardId × EpochId × BlockHeight) (fun (s, e, h) => ⟨s, e, h⟩) fun x =>
    (x.shardId, x.epochId, x.heightCreated)

/-- `ChunkEndorsementMetadata`. -/
structure ChunkEndorsementMetadata where
  accountId : AccountId
  shardId : ShardId
  epochId : EpochId
  heightCreated : BlockHeight
  deriving BEq, Inhabited

instance : Codec ChunkEndorsementMetadata :=
  .iso (AccountId × ShardId × EpochId × BlockHeight) (fun (a, s, e, h) => ⟨a, s, e, h⟩) fun x =>
    (x.accountId, x.shardId, x.epochId, x.heightCreated)

/-- `ChunkEndorsementInnerV1`: the part of an endorsement that is signed. -/
structure ChunkEndorsementInnerV1 where
  chunkHash : ChunkHash
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec ChunkEndorsementInnerV1 :=
  .iso (ChunkHash × String) (fun (c, d) => ⟨c, d⟩) fun x => (x.chunkHash, x.signatureDifferentiator)

/-- `ChunkEndorsementInnerV1::new`. -/
def ChunkEndorsementInnerV1.new (h : ChunkHash) : ChunkEndorsementInnerV1 :=
  ⟨h, "ChunkEndorsement"⟩

/-- `endorsement_signed_bytes`: the bytes that the endorsement signature covers. -/
def endorsementSignedBytes (h : ChunkHash) : ByteArray :=
  Codec.encode (ChunkEndorsementInnerV1.new h)

/-- `ChunkEndorsementV2`. -/
structure ChunkEndorsementV2 where
  inner : ChunkEndorsementInnerV1
  signature : Signature
  metadata : ChunkEndorsementMetadata
  metadataSignature : Signature
  deriving BEq, Inhabited

instance : Codec ChunkEndorsementV2 :=
  .iso (ChunkEndorsementInnerV1 × Signature × ChunkEndorsementMetadata × Signature)
    (fun (i, s, m, ms) => ⟨i, s, m, ms⟩) fun x =>
    (x.inner, x.signature, x.metadata, x.metadataSignature)

/-- `ChunkEndorsement`: V1 was deprecated, V2 has tag 1. -/
inductive ChunkEndorsement where
  | v2 (e : ChunkEndorsementV2)
  deriving BEq, Inhabited

instance : Codec ChunkEndorsement :=
  .enum "ChunkEndorsement"
    [.variant 1 ChunkEndorsementV2 .v2 fun
        | .v2 e => some e]

namespace ChunkEndorsement

/-- `ChunkEndorsement::chunk_production_key`. -/
def chunkProductionKey : ChunkEndorsement → ChunkProductionKey
  | .v2 e => ⟨e.metadata.shardId, e.metadata.epochId, e.metadata.heightCreated⟩

/-- `ChunkEndorsement::chunk_hash`. -/
def chunkHash : ChunkEndorsement → ChunkHash
  | .v2 e => e.inner.chunkHash

/-- The bytes that `signature` covers. -/
def signingBytes : ChunkEndorsement → ByteArray
  | .v2 e => endorsementSignedBytes e.inner.chunkHash

/-- The bytes that `metadata_signature` covers. -/
def metadataSigningBytes : ChunkEndorsement → ByteArray
  | .v2 e => Codec.encode e.metadata

end ChunkEndorsement

/-- `CodeHash`: the hash of some uncompiled contract code. -/
structure CodeHash where
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec CodeHash :=
  .iso CryptoHash .mk CodeHash.hash

/-- `CodeBytes`: raw contract code. -/
structure CodeBytes where
  code : ByteArray
  deriving BEq, Inhabited

instance : Codec CodeBytes :=
  .iso ByteArray .mk CodeBytes.code

/-- `CodeBytes::hash`. -/
def CodeBytes.hash (c : CodeBytes) : CodeHash :=
  ⟨CryptoHash.hash c.code⟩

/-- `EncodedChunkStateWitness`: the zstd-compressed Borsh `ChunkStateWitness`. -/
structure EncodedChunkStateWitness where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec EncodedChunkStateWitness :=
  .iso ByteArray .mk EncodedChunkStateWitness.bytes

/-- `ChunkStateWitnessAck`. -/
structure ChunkStateWitnessAck where
  chunkHash : ChunkHash
  deriving BEq, Inhabited

instance : Codec ChunkStateWitnessAck :=
  .iso ChunkHash .mk ChunkStateWitnessAck.chunkHash

/-- `ChunkStateTransition`: the base state and expected post state root of one transition. -/
structure ChunkStateTransition where
  blockHash : CryptoHash
  baseState : PartialState
  postStateRoot : CryptoHash
  deriving BEq, Inhabited

instance : Codec ChunkStateTransition :=
  .iso (CryptoHash × PartialState × CryptoHash) (fun (b, s, p) => ⟨b, s, p⟩) fun x =>
    (x.blockHash, x.baseState, x.postStateRoot)

/-- A `HashMap<ChunkHash, ReceiptProof>`: its entries, ascending by key. -/
structure ChunkReceiptProofs where
  entries : Array (ChunkHash × ReceiptProof)
  deriving BEq, Inhabited

instance : Codec ChunkReceiptProofs :=
  .isoOf (α := Array (ChunkHash × ReceiptProof))
    (.btreeMap (fun a b => compareHash a.hash b.hash) inferInstance inferInstance) .mk
    ChunkReceiptProofs.entries

/-- `ChunkStateWitnessV2`. -/
structure ChunkStateWitnessV2 where
  epochId : EpochId
  chunkHeader : ShardChunkHeader
  mainStateTransition : ChunkStateTransition
  sourceReceiptProofs : ChunkReceiptProofs
  appliedReceiptsHash : CryptoHash
  transactions : Array SignedTransaction
  implicitTransitions : Array ChunkStateTransition
  newTransactions : Array SignedTransaction
  deriving BEq, Inhabited

instance : Codec ChunkStateWitnessV2 :=
  .iso
    (EpochId ×
      ShardChunkHeader ×
      ChunkStateTransition ×
      ChunkReceiptProofs ×
      CryptoHash × Array SignedTransaction × Array ChunkStateTransition × Array SignedTransaction)
    (fun (e, h, m, s, a, t, i, n) => ⟨e, h, m, s, a, t, i, n⟩) fun x =>
    (x.epochId, x.chunkHeader, x.mainStateTransition, x.sourceReceiptProofs, x.appliedReceiptsHash,
      x.transactions, x.implicitTransitions, x.newTransactions)

/-- `ChunkStateWitness`: V1 was deprecated, V2 has tag 1. -/
inductive ChunkStateWitness where
  | v2 (w : ChunkStateWitnessV2)
  deriving BEq, Inhabited

instance : Codec ChunkStateWitness :=
  .enum "ChunkStateWitness"
    [.variant 1 ChunkStateWitnessV2 .v2 fun
        | .v2 w => some w]

namespace ChunkStateWitness

/-- `ChunkStateWitness::chunk_production_key`. -/
def chunkProductionKey : ChunkStateWitness → ChunkProductionKey
  | .v2 w => ⟨w.chunkHeader.shardId, w.epochId, w.chunkHeader.heightCreated⟩

/-- `ChunkStateWitnessAck::new`. -/
def ack : ChunkStateWitness → ChunkStateWitnessAck
  | .v2 w => ⟨w.chunkHeader.chunkHash⟩

end ChunkStateWitness

/-- `StoredChunkStateTransitionDataV1`. -/
structure StoredChunkStateTransitionDataV1 where
  baseState : PartialState
  receiptsHash : CryptoHash
  contractAccesses : Array CodeHash
  contractDeploys : Array CodeBytes
  deriving BEq, Inhabited

instance : Codec StoredChunkStateTransitionDataV1 :=
  .iso (PartialState × CryptoHash × Array CodeHash × Array CodeBytes)
    (fun (b, r, a, d) => ⟨b, r, a, d⟩) fun x =>
    (x.baseState, x.receiptsHash, x.contractAccesses, x.contractDeploys)

/-- `StoredChunkStateTransitionData`. -/
inductive StoredChunkStateTransitionData where
  | v1 (d : StoredChunkStateTransitionDataV1)
  deriving BEq, Inhabited

instance : Codec StoredChunkStateTransitionData :=
  .enum "StoredChunkStateTransitionData"
    [.variant 0 StoredChunkStateTransitionDataV1 .v1 fun
        | .v1 d => some d]

/-- `PartialEncodedStateWitnessInner`. -/
structure PartialEncodedStateWitnessInner where
  epochId : EpochId
  shardId : ShardId
  heightCreated : BlockHeight
  partOrd : UInt64
  part : ByteArray
  encodedLength : UInt64
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec PartialEncodedStateWitnessInner :=
  .iso (EpochId × ShardId × BlockHeight × UInt64 × ByteArray × UInt64 × String)
    (fun (e, s, h, o, p, l, d) => ⟨e, s, h, o, p, l, d⟩) fun x =>
    (x.epochId, x.shardId, x.heightCreated, x.partOrd, x.part, x.encodedLength,
      x.signatureDifferentiator)

/-- `PartialEncodedStateWitness`. -/
structure PartialEncodedStateWitness where
  inner : PartialEncodedStateWitnessInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec PartialEncodedStateWitness :=
  .iso (PartialEncodedStateWitnessInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `PartialEncodedStateWitnessInnerV2`: adds the previous block hash. -/
structure PartialEncodedStateWitnessInnerV2 where
  epochId : EpochId
  shardId : ShardId
  heightCreated : BlockHeight
  prevBlockHash : CryptoHash
  partOrd : UInt64
  part : ByteArray
  encodedLength : UInt64
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec PartialEncodedStateWitnessInnerV2 :=
  .iso (EpochId × ShardId × BlockHeight × CryptoHash × UInt64 × ByteArray × UInt64 × String)
    (fun (e, s, h, b, o, p, l, d) => ⟨e, s, h, b, o, p, l, d⟩) fun x =>
    (x.epochId, x.shardId, x.heightCreated, x.prevBlockHash, x.partOrd, x.part, x.encodedLength,
      x.signatureDifferentiator)

/-- `PartialEncodedStateWitnessV2`. -/
structure PartialEncodedStateWitnessV2 where
  inner : PartialEncodedStateWitnessInnerV2
  signature : Signature
  deriving BEq, Inhabited

instance : Codec PartialEncodedStateWitnessV2 :=
  .iso (PartialEncodedStateWitnessInnerV2 × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `VersionedPartialEncodedStateWitness`. -/
inductive VersionedPartialEncodedStateWitness where
  | v1 (w : PartialEncodedStateWitness)
  | v2 (w : PartialEncodedStateWitnessV2)
  deriving BEq, Inhabited

instance : Codec VersionedPartialEncodedStateWitness :=
  .enum "VersionedPartialEncodedStateWitness"
    [.variant 0 PartialEncodedStateWitness .v1 fun
        | .v1 w => some w
        | _ => none,
      .variant 1 PartialEncodedStateWitnessV2 .v2 fun
        | .v2 w => some w
        | _ => none]

namespace VersionedPartialEncodedStateWitness

/-- `chunk_production_key`. -/
def chunkProductionKey : VersionedPartialEncodedStateWitness → ChunkProductionKey
  | .v1 w => ⟨w.inner.shardId, w.inner.epochId, w.inner.heightCreated⟩
  | .v2 w => ⟨w.inner.shardId, w.inner.epochId, w.inner.heightCreated⟩

/-- The bytes that the signature covers. -/
def signingBytes : VersionedPartialEncodedStateWitness → ByteArray
  | .v1 w => Codec.encode w.inner
  | .v2 w => Codec.encode w.inner

end VersionedPartialEncodedStateWitness

/-- `MainTransitionKey`. -/
structure MainTransitionKey where
  blockHash : CryptoHash
  shardId : ShardId
  deriving BEq, Inhabited

instance : Codec MainTransitionKey :=
  .iso (CryptoHash × ShardId) (fun (b, s) => ⟨b, s⟩) fun x => (x.blockHash, x.shardId)

/-- `ChunkContractAccessesInner`. -/
structure ChunkContractAccessesInner where
  nextChunk : ChunkProductionKey
  contracts : Array CodeHash
  mainTransition : MainTransitionKey
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec ChunkContractAccessesInner :=
  .iso (ChunkProductionKey × Array CodeHash × MainTransitionKey × String)
    (fun (n, c, m, d) => ⟨n, c, m, d⟩) fun x =>
    (x.nextChunk, x.contracts, x.mainTransition, x.signatureDifferentiator)

/-- `ChunkContractAccessesV1`. -/
structure ChunkContractAccessesV1 where
  inner : ChunkContractAccessesInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec ChunkContractAccessesV1 :=
  .iso (ChunkContractAccessesInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `ChunkContractAccesses`. -/
inductive ChunkContractAccesses where
  | v1 (a : ChunkContractAccessesV1)
  deriving BEq, Inhabited

instance : Codec ChunkContractAccesses :=
  .enum "ChunkContractAccesses"
    [.variant 0 ChunkContractAccessesV1 .v1 fun
        | .v1 a => some a]

/-- The bytes that the signature covers. -/
def ChunkContractAccesses.signingBytes : ChunkContractAccesses → ByteArray
  | .v1 a => Codec.encode a.inner

/-- `ContractCodeRequestInner`. -/
structure ContractCodeRequestInner where
  requester : AccountId
  nextChunk : ChunkProductionKey
  contracts : Array CodeHash
  mainTransition : MainTransitionKey
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec ContractCodeRequestInner :=
  .iso (AccountId × ChunkProductionKey × Array CodeHash × MainTransitionKey × String)
    (fun (r, n, c, m, d) => ⟨r, n, c, m, d⟩) fun x =>
    (x.requester, x.nextChunk, x.contracts, x.mainTransition, x.signatureDifferentiator)

/-- `ContractCodeRequestV1`. -/
structure ContractCodeRequestV1 where
  inner : ContractCodeRequestInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec ContractCodeRequestV1 :=
  .iso (ContractCodeRequestInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x => (x.inner, x.signature)

/-- `ContractCodeRequest`. -/
inductive ContractCodeRequest where
  | v1 (r : ContractCodeRequestV1)
  deriving BEq, Inhabited

instance : Codec ContractCodeRequest :=
  .enum "ContractCodeRequest"
    [.variant 0 ContractCodeRequestV1 .v1 fun
        | .v1 r => some r]

/-- The bytes that the signature covers. -/
def ContractCodeRequest.signingBytes : ContractCodeRequest → ByteArray
  | .v1 r => Codec.encode r.inner

/-- `CompressedContractCode`: the zstd-compressed Borsh `Vec<CodeBytes>`. -/
structure CompressedContractCode where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec CompressedContractCode :=
  .iso ByteArray .mk CompressedContractCode.bytes

/-- `ContractCodeResponseV1`. -/
structure ContractCodeResponseV1 where
  nextChunk : ChunkProductionKey
  compressedContracts : CompressedContractCode
  deriving BEq, Inhabited

instance : Codec ContractCodeResponseV1 :=
  .iso (ChunkProductionKey × CompressedContractCode) (fun (n, c) => ⟨n, c⟩) fun x =>
    (x.nextChunk, x.compressedContracts)

/-- `ContractCodeResponseV2Inner`. -/
structure ContractCodeResponseV2Inner where
  nextChunk : ChunkProductionKey
  responder : AccountId
  compressedContracts : CompressedContractCode
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec ContractCodeResponseV2Inner :=
  .iso (ChunkProductionKey × AccountId × CompressedContractCode × String)
    (fun (n, r, c, d) => ⟨n, r, c, d⟩) fun x =>
    (x.nextChunk, x.responder, x.compressedContracts, x.signatureDifferentiator)

/-- `ContractCodeResponseV2`. -/
structure ContractCodeResponseV2 where
  inner : ContractCodeResponseV2Inner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec ContractCodeResponseV2 :=
  .iso (ContractCodeResponseV2Inner × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `ContractCodeResponse`. -/
inductive ContractCodeResponse where
  | v1 (r : ContractCodeResponseV1)
  | v2 (r : ContractCodeResponseV2)
  deriving BEq, Inhabited

instance : Codec ContractCodeResponse :=
  .enum "ContractCodeResponse"
    [.variant 0 ContractCodeResponseV1 .v1 fun
        | .v1 r => some r
        | _ => none,
      .variant 1 ContractCodeResponseV2 .v2 fun
        | .v2 r => some r
        | _ => none]

namespace ContractCodeResponse

/-- `chunk_production_key`. -/
def chunkProductionKey : ContractCodeResponse → ChunkProductionKey
  | .v1 r => r.nextChunk
  | .v2 r => r.inner.nextChunk

/-- The bytes that the signature covers; V1 is unsigned. -/
def signingBytes : ContractCodeResponse → Option ByteArray
  | .v1 _ => none
  | .v2 r => some (Codec.encode r.inner)

end ContractCodeResponse

/-- `ChunkContractDeploys`. -/
structure ChunkContractDeploys where
  compressedContracts : CompressedContractCode
  deriving BEq, Inhabited

instance : Codec ChunkContractDeploys :=
  .iso CompressedContractCode .mk ChunkContractDeploys.compressedContracts

/-- `PartialEncodedContractDeploysPart`. -/
structure PartialEncodedContractDeploysPart where
  partOrd : UInt64
  data : ByteArray
  encodedLength : UInt64
  deriving BEq, Inhabited

instance : Codec PartialEncodedContractDeploysPart :=
  .iso (UInt64 × ByteArray × UInt64) (fun (p, d, l) => ⟨p, d, l⟩) fun x =>
    (x.partOrd, x.data, x.encodedLength)

/-- `PartialEncodedContractDeploysInner`. -/
structure PartialEncodedContractDeploysInner where
  nextChunk : ChunkProductionKey
  part : PartialEncodedContractDeploysPart
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec PartialEncodedContractDeploysInner :=
  .iso (ChunkProductionKey × PartialEncodedContractDeploysPart × String)
    (fun (n, p, d) => ⟨n, p, d⟩) fun x => (x.nextChunk, x.part, x.signatureDifferentiator)

/-- `PartialEncodedContractDeploysV1`. -/
structure PartialEncodedContractDeploysV1 where
  inner : PartialEncodedContractDeploysInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec PartialEncodedContractDeploysV1 :=
  .iso (PartialEncodedContractDeploysInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `PartialEncodedContractDeploys`. -/
inductive PartialEncodedContractDeploys where
  | v1 (d : PartialEncodedContractDeploysV1)
  deriving BEq, Inhabited

instance : Codec PartialEncodedContractDeploys :=
  .enum "PartialEncodedContractDeploys"
    [.variant 0 PartialEncodedContractDeploysV1 .v1 fun
        | .v1 d => some d]

/-- The bytes that the signature covers. -/
def PartialEncodedContractDeploys.signingBytes : PartialEncodedContractDeploys → ByteArray
  | .v1 d => Codec.encode d.inner

/-- `compute_contract_accesses_hash`: the hash of the sorted, distinct code hashes. -/
def computeContractAccessesHash (accesses : Array CodeHash) : CryptoHash :=
  let sorted := accesses.qsort fun a b => compareHash a.hash b.hash == .lt
  let distinct :=
    sorted.foldl (init := #[]) fun acc h => if acc.back?.any (· == h) then acc else acc.push h
  CryptoHash.hash (distinct.foldl (fun b h => b.append h.hash.bytes) ByteArray.empty)

/-- `SpiceChunkContractAccessesInner`. -/
structure SpiceChunkContractAccessesInner where
  chunkId : SpiceChunkId
  contracts : Array CodeHash
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec SpiceChunkContractAccessesInner :=
  .iso (SpiceChunkId × Array CodeHash × String) (fun (c, a, d) => ⟨c, a, d⟩) fun x =>
    (x.chunkId, x.contracts, x.signatureDifferentiator)

/-- `SpiceChunkContractAccesses`. -/
structure SpiceChunkContractAccesses where
  inner : SpiceChunkContractAccessesInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SpiceChunkContractAccesses :=
  .iso (SpiceChunkContractAccessesInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `SpiceContractCodeRequestInner`. -/
structure SpiceContractCodeRequestInner where
  requester : AccountId
  chunkId : SpiceChunkId
  contracts : Array CodeHash
  signatureDifferentiator : String
  deriving BEq, Inhabited

instance : Codec SpiceContractCodeRequestInner :=
  .iso (AccountId × SpiceChunkId × Array CodeHash × String) (fun (r, c, a, d) => ⟨r, c, a, d⟩)
    fun x => (x.requester, x.chunkId, x.contracts, x.signatureDifferentiator)

/-- `SpiceContractCodeRequest`. -/
structure SpiceContractCodeRequest where
  inner : SpiceContractCodeRequestInner
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SpiceContractCodeRequest :=
  .iso (SpiceContractCodeRequestInner × Signature) (fun (i, s) => ⟨i, s⟩) fun x =>
    (x.inner, x.signature)

/-- `SpiceContractCodeResponseV1`. -/
structure SpiceContractCodeResponseV1 where
  chunkId : SpiceChunkId
  compressedContracts : CompressedContractCode
  deriving BEq, Inhabited

instance : Codec SpiceContractCodeResponseV1 :=
  .iso (SpiceChunkId × CompressedContractCode) (fun (c, d) => ⟨c, d⟩) fun x =>
    (x.chunkId, x.compressedContracts)

/-- `SpiceContractCodeResponse`. -/
inductive SpiceContractCodeResponse where
  | v1 (r : SpiceContractCodeResponseV1)
  deriving BEq, Inhabited

instance : Codec SpiceContractCodeResponse :=
  .enum "SpiceContractCodeResponse"
    [.variant 0 SpiceContractCodeResponseV1 .v1 fun
        | .v1 r => some r]

/-- `SpiceChunkStateTransition`. -/
structure SpiceChunkStateTransition where
  baseState : PartialState
  postStateRoot : CryptoHash
  deriving BEq, Inhabited

instance : Codec SpiceChunkStateTransition :=
  .iso (PartialState × CryptoHash) (fun (b, p) => ⟨b, p⟩) fun x => (x.baseState, x.postStateRoot)

/-- A `HashMap<ShardId, ReceiptProof>`: its entries, ascending by key. -/
structure ShardReceiptProofs where
  entries : Array (ShardId × ReceiptProof)
  deriving BEq, Inhabited

instance : Codec ShardReceiptProofs :=
  .isoOf (α := Array (ShardId × ReceiptProof)) (.btreeMap compare inferInstance inferInstance) .mk
    ShardReceiptProofs.entries

/-- `SpiceChunkStateWitnessV1`. `proof_of_invalid_chunk` is a boxed `EncodedShardChunkBody`. -/
structure SpiceChunkStateWitnessV1 where
  chunkId : SpiceChunkId
  mainStateTransition : SpiceChunkStateTransition
  sourceReceiptProofs : ShardReceiptProofs
  appliedReceiptsHash : CryptoHash
  transactions : Array SignedTransaction
  executionResultHash : ChunkExecutionResultHash
  contractAccessesHash : CryptoHash
  proofOfInvalidChunk : Option EncodedShardChunkBody
  deriving BEq, Inhabited

instance : Codec SpiceChunkStateWitnessV1 :=
  .iso
    (SpiceChunkId ×
      SpiceChunkStateTransition ×
      ShardReceiptProofs ×
      CryptoHash ×
      Array SignedTransaction ×
      ChunkExecutionResultHash × CryptoHash × Option EncodedShardChunkBody)
    (fun (c, m, s, a, t, e, h, p) => ⟨c, m, s, a, t, e, h, p⟩)
    (fun x =>
      (x.chunkId, x.mainStateTransition, x.sourceReceiptProofs, x.appliedReceiptsHash,
        x.transactions, x.executionResultHash, x.contractAccessesHash, x.proofOfInvalidChunk))

/-- `SpiceChunkStateWitness`. -/
inductive SpiceChunkStateWitness where
  | v1 (w : SpiceChunkStateWitnessV1)
  deriving BEq, Inhabited

instance : Codec SpiceChunkStateWitness :=
  .enum "SpiceChunkStateWitness"
    [.variant 0 SpiceChunkStateWitnessV1 .v1 fun
        | .v1 w => some w]

/-- `SpiceDataIdentifier`. -/
inductive SpiceDataIdentifier where
  | receiptProof (blockHash : CryptoHash) (fromShardId toShardId : ShardId)
  | witness (blockHash : CryptoHash) (shardId : ShardId)
  deriving BEq, Inhabited

instance : Codec SpiceDataIdentifier :=
  .enum "SpiceDataIdentifier"
    [.variant 0 (CryptoHash × ShardId × ShardId) (fun (b, f, t) => .receiptProof b f t) fun
        | .receiptProof b f t => some (b, f, t)
        | _ => none,
      .variant 1 (CryptoHash × ShardId) (fun (b, s) => .witness b s) fun
        | .witness b s => some (b, s)
        | _ => none]

/-- `SpiceDataCommitment`. -/
structure SpiceDataCommitment where
  hash : CryptoHash
  root : CryptoHash
  encodedLength : UInt64
  deriving BEq, Inhabited

instance : Codec SpiceDataCommitment :=
  .iso (CryptoHash × CryptoHash × UInt64) (fun (h, r, l) => ⟨h, r, l⟩) fun x =>
    (x.hash, x.root, x.encodedLength)

/-- `SpiceDataPart`. -/
structure SpiceDataPart where
  partOrd : UInt64
  part : ByteArray
  merkleProof : Array MerklePathItem
  deriving BEq, Inhabited

instance : Codec SpiceDataPart :=
  .iso (UInt64 × ByteArray × Array MerklePathItem) (fun (o, p, m) => ⟨o, p, m⟩) fun x =>
    (x.partOrd, x.part, x.merkleProof)

/-- `SpicePartialDataInner`. -/
structure SpicePartialDataInner where
  id : SpiceDataIdentifier
  commitment : SpiceDataCommitment
  parts : Array SpiceDataPart
  deriving BEq, Inhabited

instance : Codec SpicePartialDataInner :=
  .iso (SpiceDataIdentifier × SpiceDataCommitment × Array SpiceDataPart)
    (fun (i, c, p) => ⟨i, c, p⟩) fun x => (x.id, x.commitment, x.parts)

/-- `SpicePartialDataInner::serialize_for_signing`: the pair of the data and its differentiator. -/
def SpicePartialDataInner.signingBytes (i : SpicePartialDataInner) : ByteArray :=
  Codec.encode (i, "SpicePartialData")

/-- `SpicePartialData`. -/
structure SpicePartialData where
  inner : SpicePartialDataInner
  sender : AccountId
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SpicePartialData :=
  .iso (SpicePartialDataInner × AccountId × Signature) (fun (i, s, g) => ⟨i, s, g⟩) fun x =>
    (x.inner, x.sender, x.signature)

/-- `SpiceVerifiedPartialData`. -/
structure SpiceVerifiedPartialData where
  id : SpiceDataIdentifier
  commitment : SpiceDataCommitment
  parts : Array SpiceDataPart
  sender : AccountId
  deriving BEq, Inhabited

instance : Codec SpiceVerifiedPartialData :=
  .iso (SpiceDataIdentifier × SpiceDataCommitment × Array SpiceDataPart × AccountId)
    (fun (i, c, p, s) => ⟨i, c, p, s⟩) fun x => (x.id, x.commitment, x.parts, x.sender)

end Near.Node
