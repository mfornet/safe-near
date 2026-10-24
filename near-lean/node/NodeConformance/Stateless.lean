import NodeConformance.Runner
import NearNode.Primitives

/-!
The M1c part of the registry of `node-conformance-types` for stateless validation: chunk
endorsements, witnesses, partial witnesses and the contract-distribution messages, with their
signing bytes and production keys.
-/

open Near.Node Near.Node.Conformance Near.Node.Borsh

private def sigData (b : ByteArray) : List (String × ByteArray) :=
  [("sigData", b)]

private def keyOf (k : ChunkProductionKey) : List (String × ByteArray) :=
  [("key", Codec.encode k)]

/-- Every stateless validation fixture type with its check. -/
def statelessRegistry : List (String × Check) :=
  [("ChunkProductionKey", check ChunkProductionKey),
    ("ChunkEndorsement",
      check ChunkEndorsement fun e =>
        sigData e.signingBytes ++ [("metaSigData", e.metadataSigningBytes)] ++
          keyOf e.chunkProductionKey),
    ("ChunkStateWitnessAck", check ChunkStateWitnessAck),
    ("ChunkStateTransition", check ChunkStateTransition),
    ("ChunkStateWitness",
      check ChunkStateWitness fun w => keyOf w.chunkProductionKey ++ [("ack", Codec.encode w.ack)]),
    ("EncodedChunkStateWitness", check EncodedChunkStateWitness),
    ("StoredChunkStateTransitionData", check StoredChunkStateTransitionData),
    ("CodeHash", check CodeHash),
    ("CodeBytes", check CodeBytes fun c => [("hash", c.hash.hash.bytes)]),
    ("CodeHashes",
      check (Array CodeHash) fun v => [("hash", (computeContractAccessesHash v).bytes)]),
    ("PartialEncodedStateWitness",
      check PartialEncodedStateWitness fun w => sigData (Codec.encode w.inner)),
    ("PartialEncodedStateWitnessV2",
      check PartialEncodedStateWitnessV2 fun w => sigData (Codec.encode w.inner)),
    ("VersionedPartialEncodedStateWitness",
      check VersionedPartialEncodedStateWitness fun w =>
        sigData w.signingBytes ++ keyOf w.chunkProductionKey),
    ("MainTransitionKey", check MainTransitionKey),
    ("ChunkContractAccesses", check ChunkContractAccesses fun a => sigData a.signingBytes),
    ("ContractCodeRequest", check ContractCodeRequest fun r => sigData r.signingBytes),
    ("ContractCodeResponseV1", check ContractCodeResponseV1),
    ("ContractCodeResponseV2",
      check ContractCodeResponseV2 fun r => sigData (Codec.encode r.inner)),
    ("ContractCodeResponse",
      check ContractCodeResponse fun r =>
        keyOf r.chunkProductionKey ++ (r.signingBytes.toList.flatMap sigData)),
    ("ChunkContractDeploys", check ChunkContractDeploys),
    ("PartialEncodedContractDeploysPart", check PartialEncodedContractDeploysPart),
    ("PartialEncodedContractDeploys",
      check PartialEncodedContractDeploys fun d => sigData d.signingBytes),
    ("SpiceChunkContractAccesses",
      check SpiceChunkContractAccesses fun a => sigData (Codec.encode a.inner)),
    ("SpiceContractCodeRequest",
      check SpiceContractCodeRequest fun r => sigData (Codec.encode r.inner)),
    ("SpiceContractCodeResponse", check SpiceContractCodeResponse),
    ("SpiceChunkStateWitness", check SpiceChunkStateWitness),
    ("SpiceDataIdentifier", check SpiceDataIdentifier),
    ("SpiceDataCommitment", check SpiceDataCommitment), ("SpiceDataPart", check SpiceDataPart),
    ("SpicePartialData", check SpicePartialData fun d => sigData d.inner.signingBytes),
    ("SpiceVerifiedPartialData", check SpiceVerifiedPartialData)]
