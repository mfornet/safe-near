import NearNode.Primitives.ChunkExtra

/-!
# Spice execution results and endorsements

`near-primitives::types` (`SpiceChunkId`, `ChunkExecutionResult`) and `spice::chunk_endorsement` at
`=0.37.4`, carried by spice blocks. Endorsements are signed over the Borsh pair of the
`SpiceEndorsementSignedData` and the string `"SpiceChunkEndorsement"`.
-/

namespace Near.Node

open Borsh

/-- `SpiceChunkId`: block hash and shard identify a chunk, since missing chunks are empty. -/
structure SpiceChunkId where
  blockHash : CryptoHash
  shardId : ShardId
  deriving BEq, Inhabited

instance : Codec SpiceChunkId :=
  .iso (CryptoHash × ShardId) (fun (b, s) => ⟨b, s⟩) fun x => (x.blockHash, x.shardId)

/-- `ChunkExecutionResult`. -/
structure ChunkExecutionResult where
  chunkExtra : ChunkExtra
  outgoingReceiptsRoot : CryptoHash
  deriving BEq, Inhabited

instance : Codec ChunkExecutionResult :=
  .iso (ChunkExtra × CryptoHash) (fun (c, o) => ⟨c, o⟩) fun x =>
    (x.chunkExtra, x.outgoingReceiptsRoot)

/-- `ChunkExecutionResultHash`. -/
structure ChunkExecutionResultHash where
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec ChunkExecutionResultHash :=
  .iso CryptoHash .mk ChunkExecutionResultHash.hash

/-- `ChunkExecutionResult::compute_hash`. -/
def ChunkExecutionResult.computeHash (r : ChunkExecutionResult) : ChunkExecutionResultHash :=
  ⟨CryptoHash.hashBorsh r⟩

/-- `SpiceEndorsementSignedData`. -/
structure SpiceEndorsementSignedData where
  executionResultHash : ChunkExecutionResultHash
  chunkId : SpiceChunkId
  deriving BEq, Inhabited

instance : Codec SpiceEndorsementSignedData :=
  .iso (ChunkExecutionResultHash × SpiceChunkId) (fun (e, c) => ⟨e, c⟩) fun x =>
    (x.executionResultHash, x.chunkId)

/-- `SpiceEndorsementSignedData::serialize_data_for_signing`: the Borsh pair of the data and the
signature differentiator. -/
def SpiceEndorsementSignedData.dataForSigning (d : SpiceEndorsementSignedData) : ByteArray :=
  Codec.encode (d, "SpiceChunkEndorsement")

/-- `SpiceEndorsementCoreStatement`. -/
structure SpiceEndorsementCoreStatement where
  accountId : AccountId
  signature : Signature
  signedData : SpiceEndorsementSignedData
  deriving BEq, Inhabited

instance : Codec SpiceEndorsementCoreStatement :=
  .iso (AccountId × Signature × SpiceEndorsementSignedData) (fun (a, s, d) => ⟨a, s, d⟩) fun x =>
    (x.accountId, x.signature, x.signedData)

/-- `SpiceCoreStatement`: an endorsement or a chunk execution result. -/
inductive SpiceCoreStatement where
  | endorsement (e : SpiceEndorsementCoreStatement)
  | chunkExecutionResult (chunkId : SpiceChunkId) (executionResult : ChunkExecutionResult)
  deriving BEq, Inhabited

instance : Codec SpiceCoreStatement :=
  .enum "SpiceCoreStatement"
    [.variant 0 SpiceEndorsementCoreStatement .endorsement fun
        | .endorsement e => some e
        | _ => none,
      .variant 1 (SpiceChunkId × ChunkExecutionResult) (fun (i, r) => .chunkExecutionResult i r) fun
        | .chunkExecutionResult i r => some (i, r)
        | _ => none]

/-- `SpiceCoreStatements`. -/
structure SpiceCoreStatements where
  statements : Array SpiceCoreStatement
  deriving BEq, Inhabited

instance : Codec SpiceCoreStatements :=
  .iso (Array SpiceCoreStatement) .mk SpiceCoreStatements.statements

/-- `SpiceStoredVerifiedEndorsement`. -/
structure SpiceStoredVerifiedEndorsement where
  executionResultHash : ChunkExecutionResultHash
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SpiceStoredVerifiedEndorsement :=
  .iso (ChunkExecutionResultHash × Signature) (fun (e, s) => ⟨e, s⟩) fun x =>
    (x.executionResultHash, x.signature)

/-- `SpiceChunkEndorsementV1`. -/
structure SpiceChunkEndorsementV1 where
  executionResult : ChunkExecutionResult
  chunkId : SpiceChunkId
  accountId : AccountId
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SpiceChunkEndorsementV1 :=
  .iso (ChunkExecutionResult × SpiceChunkId × AccountId × Signature)
    (fun (e, c, a, s) => ⟨e, c, a, s⟩) fun x =>
    (x.executionResult, x.chunkId, x.accountId, x.signature)

/-- The data that a `SpiceChunkEndorsementV1` signature covers. -/
def SpiceChunkEndorsementV1.signedData (e : SpiceChunkEndorsementV1) : SpiceEndorsementSignedData :=
  ⟨e.executionResult.computeHash, e.chunkId⟩

/-- `SpiceChunkEndorsement`: only V1 exists. -/
inductive SpiceChunkEndorsement where
  | v1 (e : SpiceChunkEndorsementV1)
  deriving BEq, Inhabited

instance : Codec SpiceChunkEndorsement :=
  .enum "SpiceChunkEndorsement"
    [.variant 0 SpiceChunkEndorsementV1 .v1 fun
        | .v1 e => some e]

/-- `SpiceUncertifiedChunkInfo`. -/
structure SpiceUncertifiedChunkInfo where
  chunkId : SpiceChunkId
  missingEndorsements : Array AccountId
  presentEndorsements : Array (AccountId × SpiceStoredVerifiedEndorsement)
  deriving BEq, Inhabited

instance : Codec SpiceUncertifiedChunkInfo :=
  .iso (SpiceChunkId × Array AccountId × Array (AccountId × SpiceStoredVerifiedEndorsement))
    (fun (c, m, p) => ⟨c, m, p⟩) fun x => (x.chunkId, x.missingEndorsements, x.presentEndorsements)

end Near.Node
