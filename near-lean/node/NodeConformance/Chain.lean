import NodeConformance.Runner
import NearNode.Primitives

/-!
The M1b part of the registry of `node-conformance-types`: blocks, headers, approvals, chunks,
challenges and spice types, with their derived values (hashes, signing bytes, roots).
-/

open Near.Node Near.Node.Conformance Near.Node.Borsh

private def hashOf (h : CryptoHash) : List (String × ByteArray) :=
  [("hash", h.bytes)]

private def byte (n : UInt8) : ByteArray :=
  ⟨#[n]⟩

/-- Merkle root and proofs of a list of items. -/
private def merkleFields [Codec α] (items : Array α) : List (String × ByteArray) :=
  let (root, paths) := merklize items
  [("hash", root.bytes), ("paths", Codec.encode paths)]

private def chunkHashFields (h : ChunkHash) (inner : CryptoHash) : List (String × ByteArray) :=
  [("hash", h.hash.bytes), ("innerHash", inner.bytes)]

/-- `hash` and `innerHash` of a block header. -/
private def headerFields [Codec ρ] (prev : CryptoHash) (lite : BlockHeaderInnerLite) (rest : ρ) :
    List (String × ByteArray) :=
  [("hash", (computeBlockHash prev lite rest).bytes),
    ("innerHash", (computeInnerHash lite rest).bytes)]

/-- The root and proofs are present only when every part is. -/
private def bodyFields (b : EncodedShardChunkBody) : List (String × ByteArray) :=
  match b.merkleHashAndPaths with
  | some (root, paths) => [("root", root.bytes), ("paths", Codec.encode paths)]
  | none => []

private def blockFields (b : Block) : List (String × ByteArray) :=
  let (headersRoot, paths) := b.computeChunkHeadersRoot
  [("hash", b.hash.bytes)] ++ (b.computeBlockBodyHash.toList.map fun h => ("bodyHash", h.bytes)) ++
    [("stateRoot", b.computeStateRoot.bytes),
      ("receiptsRoot", b.computeChunkPrevOutgoingReceiptsRoot.bytes),
      ("chunkHeadersRoot", headersRoot.bytes), ("chunkHeadersPaths", Codec.encode paths),
      ("txRoot", b.computeChunkTxRoot.bytes), ("outcomeRoot", b.computeOutcomeRoot.bytes),
      ("validity", byte (BlockValidityError.code b.checkValidity))]

/-- Every M1b fixture type with its check. -/
def chainRegistry : List (String × Check) :=
  [("EpochId", check EpochId), ("ValidatorStakeV1", check ValidatorStakeV1),
    ("ValidatorStake", check ValidatorStake),
    ("ValidatorStakes",
      check (Array ValidatorStake) fun v =>
        [("hash", (bpHash v).bytes), ("hashV1", (bpHashV1 v).bytes)]),
    ("SlashedValidator", check SlashedValidator),
    ("SpiceChunkEndorsementStats", check SpiceChunkEndorsementStats),
    ("TrieSplit", check TrieSplit), ("ChunkEndorsementsBitmap", check ChunkEndorsementsBitmap),
    ("CongestionInfoV1", check CongestionInfoV1), ("CongestionInfo", check CongestionInfo),
    ("BandwidthRequestBitmap", check BandwidthRequestBitmap),
    ("BandwidthRequest", check BandwidthRequest),
    ("BandwidthRequestsV1", check BandwidthRequestsV1),
    ("BandwidthRequests", check BandwidthRequests), ("LinkAllowance", check LinkAllowance),
    ("BandwidthSchedulerStateV1", check BandwidthSchedulerStateV1),
    ("BandwidthSchedulerState", check BandwidthSchedulerState),
    ("BandwidthSchedulerParams", check BandwidthSchedulerParams), ("ChunkExtra", check ChunkExtra),
    ("HashList", check (Array CryptoHash) merkleFields),
    ("BytesList", check (Array ByteArray) merkleFields),
    ("PartialMerkleTree",
      check PartialMerkleTree fun t =>
        [("hash", t.root.bytes), ("wellFormed", byte (if t.isWellFormed then 1 else 0))] ++
          if t.isWellFormed then [("inserted", Codec.encode (t.insert (CryptoHash.hash (byte 7))))]
          else []),
    ("ApprovalInner", check ApprovalInner),
    ("Approval", check Approval fun a => [("sigData", a.sigData)]),
    ("ApprovalMessage", check ApprovalMessage fun a => [("sigData", a.approval.sigData)]),
    ("ChunkHash", check ChunkHash),
    ("ChunkHashHeight", check ChunkHashHeight fun c => hashOf (CryptoHash.hashBorsh c)),
    ("ShardChunkHeaderInnerV1", check ShardChunkHeaderInnerV1),
    ("ShardChunkHeaderInnerV2", check ShardChunkHeaderInnerV2),
    ("ShardChunkHeaderInnerV3", check ShardChunkHeaderInnerV3),
    ("ShardChunkHeaderInnerV4", check ShardChunkHeaderInnerV4),
    ("ShardChunkHeaderInnerV5", check ShardChunkHeaderInnerV5),
    ("ShardChunkHeaderInnerV6", check ShardChunkHeaderInnerV6),
    ("ShardChunkHeaderInner", check ShardChunkHeaderInner fun i => hashOf (CryptoHash.hashBorsh i)),
    ("ShardChunkHeaderV1",
      check ShardChunkHeaderV1 fun c => chunkHashFields c.chunkHash (CryptoHash.hashBorsh c.inner)),
    ("ShardChunkHeaderV2",
      check ShardChunkHeaderV2 fun c => chunkHashFields c.chunkHash (CryptoHash.hashBorsh c.inner)),
    ("ShardChunkHeaderV3",
      check ShardChunkHeaderV3 fun c => chunkHashFields c.chunkHash (CryptoHash.hashBorsh c.inner)),
    ("ShardChunkHeader",
      check ShardChunkHeader fun c => chunkHashFields c.chunkHash c.innerHeaderHash),
    ("ShardProof", check ShardProof),
    ("ReceiptProof",
      check ReceiptProof fun p =>
        [("hash", p.leafHash.bytes),
          ("root", (computeRootFromPath p.proof.proof (CryptoHash.hashBorsh p.leafHash)).bytes)]),
    ("PartialEncodedChunkPart", check PartialEncodedChunkPart),
    ("PartialEncodedChunkV1", check PartialEncodedChunkV1 fun c => hashOf c.header.chunkHash.hash),
    ("PartialEncodedChunkV2", check PartialEncodedChunkV2 fun c => hashOf c.header.chunkHash.hash),
    ("PartialEncodedChunk", check PartialEncodedChunk fun c => hashOf c.chunkHash.hash),
    ("ShardChunkV1", check ShardChunkV1 fun c => hashOf c.header.chunkHash.hash),
    ("ShardChunkV2", check ShardChunkV2 fun c => hashOf c.header.chunkHash.hash),
    ("ShardChunk", check ShardChunk fun c => hashOf c.computeHeaderHash.hash),
    ("EncodedShardChunkBody", check EncodedShardChunkBody bodyFields),
    ("EncodedShardChunkV1", check EncodedShardChunkV1 fun c => hashOf c.header.chunkHash.hash),
    ("EncodedShardChunkV2", check EncodedShardChunkV2 fun c => hashOf c.header.chunkHash.hash),
    ("EncodedShardChunk",
      check EncodedShardChunk fun c => hashOf c.chunkHash.hash ++ bodyFields c.content),
    ("TransactionReceipt", check TransactionReceipt), ("StateSyncInfoV0", check StateSyncInfoV0),
    ("StateSyncInfoV1", check StateSyncInfoV1), ("StateSyncInfo", check StateSyncInfo),
    ("PartialState", check PartialState), ("BlockHeaderInnerLite", check BlockHeaderInnerLite),
    ("BlockHeaderInnerRest", check BlockHeaderInnerRestV1),
    ("BlockHeaderInnerRestV2", check BlockHeaderInnerRestV2),
    ("BlockHeaderInnerRestV3", check BlockHeaderInnerRestV3),
    ("BlockHeaderInnerRestV4", check BlockHeaderInnerRestV4),
    ("BlockHeaderInnerRestV5", check BlockHeaderInnerRestV5),
    ("BlockHeaderInnerRestV6", check BlockHeaderInnerRestV6),
    ("BlockHeaderInnerRestV7", check BlockHeaderInnerRestV7),
    ("BlockHeaderV1", check BlockHeaderV1 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeaderV2", check BlockHeaderV2 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeaderV3", check BlockHeaderV3 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeaderV4", check BlockHeaderV4 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeaderV5", check BlockHeaderV5 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeaderV6", check BlockHeaderV6 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeaderV7", check BlockHeaderV7 fun h => headerFields h.prevHash h.innerLite h.innerRest),
    ("BlockHeader",
      check BlockHeader fun h => [("hash", h.hash.bytes), ("innerHash", h.innerHash.bytes)]),
    ("SpiceChunkId", check SpiceChunkId),
    ("ChunkExecutionResult", check ChunkExecutionResult fun r => hashOf r.computeHash.hash),
    ("ChunkExecutionResultHash", check ChunkExecutionResultHash),
    ("SpiceEndorsementSignedData",
      check SpiceEndorsementSignedData fun d => [("sigData", d.dataForSigning)]),
    ("SpiceEndorsementCoreStatement", check SpiceEndorsementCoreStatement),
    ("SpiceCoreStatement", check SpiceCoreStatement),
    ("SpiceCoreStatements", check SpiceCoreStatements),
    ("SpiceStoredVerifiedEndorsement", check SpiceStoredVerifiedEndorsement),
    ("SpiceChunkEndorsement", check SpiceChunkEndorsement),
    ("SpiceUncertifiedChunkInfo", check SpiceUncertifiedChunkInfo),
    ("BlockDoubleSign", check BlockDoubleSign),
    ("MaybeEncodedShardChunk", check MaybeEncodedShardChunk), ("ChunkProofs", check ChunkProofs),
    ("ChunkState", check ChunkState), ("ChallengeBody", check ChallengeBody),
    ("Challenge", check Challenge fun c => hashOf c.hash),
    ("BlockBodyV1", check BlockBodyV1 fun b => hashOf (BlockBody.v1 b).computeHash),
    ("BlockBodyV2", check BlockBodyV2), ("SpiceBlockBodyV3", check SpiceBlockBodyV3),
    ("BlockBody", check BlockBody fun b => hashOf b.computeHash),
    ("BlockV1", check BlockV1 fun b => blockFields (.v1 b)),
    ("BlockV2", check BlockV2 fun b => blockFields (.v2 b)),
    ("BlockV3", check BlockV3 fun b => blockFields (.v3 b)),
    ("BlockV4", check BlockV4 fun b => blockFields (.v4 b)), ("Block", check Block blockFields),
    ("Tip", check Tip), ("OptimisticBlockInner", check OptimisticBlockInner),
    ("OptimisticBlock", check OptimisticBlock fun b => hashOf b.hash)]
