import NearNode.Primitives
import NearNode.Validator.Signer
import NearNode.Validator.ReedSolomon

/-!
# The signed messages of a validator

The constructors of `near-primitives` that sign with the validator key:

* `Approval::new` (`block_header.rs`): an `Endorsement(parent_hash)` when the target is the child of
  the parent, a `Skip(parent_height)` otherwise, signed over `get_data_for_sig`;
* `ChunkEndorsement::new` (`stateless_validation/chunk_endorsement.rs`): the signature over the chunk
  hash with the differentiator `"ChunkEndorsement"` and the signature over the Borsh metadata
  (account, shard, epoch, height created);
* `PartialEncodedStateWitness::new` (`partial_witness.rs`), at protocol 86 always the V1 form
  (`VersionedPartialEncodedStateWitness::new` drops the protocol version), signed over the Borsh
  inner part with the differentiator `"PartialEncodedStateWitness"`;
* `ChunkStateWitnessAck::new`.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Borsh

/-- `ApprovalInner::new`. -/
def approvalInner (parentHash : CryptoHash) (parentHeight targetHeight : BlockHeight) :
    ApprovalInner :=
  if targetHeight == parentHeight + 1 then .endorsement parentHash else .skip parentHeight

/-- `Approval::new`. -/
def newApproval (s : Signer) (parentHash : CryptoHash) (parentHeight targetHeight : BlockHeight) :
    Approval :=
  let inner := approvalInner parentHash parentHeight targetHeight
  { inner, targetHeight, signature := s.sign (Approval.getDataForSig inner targetHeight),
    accountId := s.accountId }

/-- `ChunkEndorsement::new`. -/
def newChunkEndorsement (s : Signer) (epochId : EpochId) (header : ShardChunkHeader) :
    ChunkEndorsement :=
  let metadata : ChunkEndorsementMetadata :=
    ⟨s.accountId, header.shardId, epochId, header.heightCreated⟩
  let inner := ChunkEndorsementInnerV1.new header.chunkHash
  .v2
    { inner, signature := s.sign (endorsementSignedBytes header.chunkHash), metadata,
      metadataSignature := s.sign (Codec.encode metadata) }

/-- `PartialEncodedStateWitness::new`. -/
def newPartialWitness (s : Signer) (epochId : EpochId) (header : ShardChunkHeader) (partOrd : Nat)
    (part : ByteArray) (encodedLength : Nat) : PartialEncodedStateWitness :=
  let inner : PartialEncodedStateWitnessInner :=
    ⟨epochId, header.shardId, header.heightCreated, partOrd.toUInt64, part, encodedLength.toUInt64,
      "PartialEncodedStateWitness"⟩
  ⟨inner, s.sign (Codec.encode inner)⟩

end Near.Node.Validator
