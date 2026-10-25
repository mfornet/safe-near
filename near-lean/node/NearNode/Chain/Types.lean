import NearNode.Primitives
import NearCrypto.Ed25519
import NearCrypto.Secp256k1
import NearCrypto.Vrf
import NearCrypto.MlDsa.Impl

/-!
# Chain validation: errors, header views and signatures

The shared vocabulary of header and block validation (`chain/chain/src/chain.rs`,
`chain/chain/src/signature_verification.rs` at the pinned nearcore). A rejection is an `Err`: the
name of the `near_chain_primitives::Error` variant that nearcore returns, so the harness compares
the kind of a verdict and not its text; `Error::Other` carries its message as the kind's detail.
-/

namespace Near.Node

open Borsh

/-! ### Validators -/

/-- The account, key and stake of a validator. -/
def ValidatorStake.accountId : ValidatorStake → AccountId
  | .v1 v => v.accountId

def ValidatorStake.publicKey : ValidatorStake → PublicKey
  | .v1 v => v.publicKey

def ValidatorStake.stake : ValidatorStake → Balance
  | .v1 v => v.stake

/-- `EpochInfo::get_validator`. -/
def EpochInfo.getValidator (e : EpochInfo) (id : ValidatorId) : Option ValidatorStake :=
  match e with
  | .v1 e => (e.validators[id.toNat]?).map fun v => .v1 v
  | .v2 e => e.validators[id.toNat]?
  | .v3 e => e.base.validators[id.toNat]?
  | .v4 e => e.validators[id.toNat]?
  | .v5 e => e.validators[id.toNat]?

/-- `EpochInfo::get_validator_by_account`. -/
def EpochInfo.getValidatorByAccount (e : EpochInfo) (a : AccountId) : Option ValidatorStake :=
  (e.getValidatorId a).bind e.getValidator

/-- `EpochInfo::minted_amount`. -/
def EpochInfo.mintedAmount : EpochInfo → Balance
  | .v1 e => e.mintedAmount
  | .v2 e => e.mintedAmount
  | .v3 e => e.base.mintedAmount
  | .v4 e => e.mintedAmount
  | .v5 e => e.mintedAmount

/-- The version number of an `EpochInfo`. -/
def EpochInfo.version : EpochInfo → Nat
  | .v1 _ => 1
  | .v2 _ => 2
  | .v3 _ => 3
  | .v4 _ => 4
  | .v5 _ => 5

/-! ### Chunk headers -/

/-- The previous block a chunk was built on. -/
def ShardChunkHeaderInner.prevBlockHashOf : ShardChunkHeaderInner → CryptoHash
  | .v1 i => i.prevBlockHash
  | .v2 i => i.prevBlockHash
  | .v3 i => i.prevBlockHash
  | .v4 i => i.prevBlockHash
  | .v5 i => i.prevBlockHash
  | .v6 i => i.prevBlockHash

/-- `ShardChunkHeader::prev_block_hash`. -/
def ShardChunkHeader.prevBlockHash : ShardChunkHeader → CryptoHash
  | .v1 h => h.inner.prevBlockHash
  | .v2 h => h.inner.prevBlockHash
  | .v3 h => h.inner.prevBlockHashOf

/-- `ShardChunkHeader::is_genesis`. -/
def ShardChunkHeader.isGenesis (h : ShardChunkHeader) : Bool :=
  h.prevBlockHash == CryptoHash.zero

/-- `ShardChunkHeader::prev_gas_used`. -/
def ShardChunkHeader.prevGasUsed : ShardChunkHeader → Gas
  | .v1 h => h.inner.prevGasUsed
  | .v2 h => h.inner.prevGasUsed
  | .v3 h =>
    match h.inner with
    | .v1 i => i.prevGasUsed
    | .v2 i => i.prevGasUsed
    | .v3 i => i.prevGasUsed
    | .v4 i => i.prevGasUsed
    | .v5 i => i.prevGasUsed
    | .v6 _ => 0

/-- `ShardChunkHeader::gas_limit`. -/
def ShardChunkHeader.gasLimit : ShardChunkHeader → Gas
  | .v1 h => h.inner.gasLimit
  | .v2 h => h.inner.gasLimit
  | .v3 h =>
    match h.inner with
    | .v1 i => i.gasLimit
    | .v2 i => i.gasLimit
    | .v3 i => i.gasLimit
    | .v4 i => i.gasLimit
    | .v5 i => i.gasLimit
    | .v6 _ => 0

/-- `ShardChunkHeader::prev_balance_burnt`. -/
def ShardChunkHeader.prevBalanceBurnt : ShardChunkHeader → Balance
  | .v1 h => h.inner.prevBalanceBurnt
  | .v2 h => h.inner.prevBalanceBurnt
  | .v3 h =>
    match h.inner with
    | .v1 i => i.prevBalanceBurnt
    | .v2 i => i.prevBalanceBurnt
    | .v3 i => i.prevBalanceBurnt
    | .v4 i => i.prevBalanceBurnt
    | .v5 i => i.prevBalanceBurnt
    | .v6 _ => 0

/-- `ShardChunkHeader::prev_validator_proposals`, lifted to `ValidatorStake`. -/
def ShardChunkHeader.prevValidatorProposals : ShardChunkHeader → Array ValidatorStake
  | .v1 h => h.inner.prevValidatorProposals.map .v1
  | .v2 h => h.inner.prevValidatorProposals.map .v1
  | .v3 h =>
    match h.inner with
    | .v1 i => i.prevValidatorProposals.map .v1
    | .v2 i => i.prevValidatorProposals
    | .v3 i => i.prevValidatorProposals
    | .v4 i => i.prevValidatorProposals
    | .v5 i => i.prevValidatorProposals
    | .v6 _ => #[]

/-! ### Blocks -/

/-- `Block::vrf_value` and `vrf_proof`. -/
def Block.vrf : Block → VrfValue × VrfProof
  | .v1 b => (b.vrfValue, b.vrfProof)
  | .v2 b => (b.vrfValue, b.vrfProof)
  | .v3 b => (b.body.vrfValue, b.body.vrfProof)
  | .v4 b =>
    match b.body with
    | .v1 x => (x.vrfValue, x.vrfProof)
    | .v2 x => (x.vrfValue, x.vrfProof)
    | .v3 x => (x.vrfValue, x.vrfProof)

/-- `Block::chunk_endorsements`: the signatures of the chunk validators, per shard. Empty before
body V2. -/
def Block.chunkEndorsements : Block → Array (Array (Option Signature))
  | .v4 ⟨_, .v2 b⟩ => b.chunkEndorsements
  | _ => #[]

/-- `Block::is_genesis`-style test on the header. -/
def Block.prevHash (b : Block) : CryptoHash :=
  b.header.prevHash

/-! ### Headers -/

/-- The fields of a block header that validation reads, whatever the version. Versions 4 to 6 are
the ones a protocol 86 chain produces (V7 is SPICE, earlier ones predate `block_body_hash`). -/
structure HeaderView where
  prevHash : CryptoHash
  signature : Signature
  height : BlockHeight
  epochId : EpochId
  nextEpochId : EpochId
  prevStateRoot : CryptoHash
  prevOutcomeRoot : CryptoHash
  timestamp : UInt64
  nextBpHash : CryptoHash
  blockMerkleRoot : CryptoHash
  blockBodyHash : CryptoHash
  prevChunkOutgoingReceiptsRoot : CryptoHash
  chunkHeadersRoot : CryptoHash
  chunkTxRoot : CryptoHash
  challengesPresent : Bool
  randomValue : CryptoHash
  prevValidatorProposals : Array ValidatorStake
  chunkMask : Array Bool
  nextGasPrice : Balance
  totalSupply : Balance
  lastFinalBlock : CryptoHash
  lastDsFinalBlock : CryptoHash
  blockOrdinal : UInt64
  prevHeight : BlockHeight
  epochSyncDataHash : Option CryptoHash
  approvals : Array (Option Signature)
  latestProtocolVersion : ProtocolVersion
  chunkEndorsements : Option ChunkEndorsementsBitmap
  shardSplit : Option (ShardId × AccountId)
  deriving Inhabited

/-- The view of a header, or `none` for the versions this node does not validate. -/
def BlockHeader.view? : BlockHeader → Option HeaderView
  | .v4 h =>
    let r := h.innerRest
    some
      { prevHash := h.prevHash, signature := h.signature, height := h.innerLite.height,
        epochId := h.innerLite.epochId, nextEpochId := h.innerLite.nextEpochId,
        prevStateRoot := h.innerLite.prevStateRoot, prevOutcomeRoot := h.innerLite.prevOutcomeRoot,
        timestamp := h.innerLite.timestamp, nextBpHash := h.innerLite.nextBpHash,
        blockMerkleRoot := h.innerLite.blockMerkleRoot, blockBodyHash := r.blockBodyHash,
        prevChunkOutgoingReceiptsRoot := r.prevChunkOutgoingReceiptsRoot,
        chunkHeadersRoot := r.chunkHeadersRoot, chunkTxRoot := r.chunkTxRoot,
        challengesPresent := !r.challengesResult.isEmpty || r.challengesRoot != CryptoHash.zero,
        randomValue := r.randomValue, prevValidatorProposals := r.prevValidatorProposals,
        chunkMask := r.chunkMask, nextGasPrice := r.nextGasPrice, totalSupply := r.totalSupply,
        lastFinalBlock := r.lastFinalBlock, lastDsFinalBlock := r.lastDsFinalBlock,
        blockOrdinal := r.blockOrdinal, prevHeight := r.prevHeight,
        epochSyncDataHash := r.epochSyncDataHash, approvals := r.approvals,
        latestProtocolVersion := r.latestProtocolVersion, chunkEndorsements := none,
        shardSplit := none }
  | .v5 h =>
    let r := h.innerRest
    some
      { prevHash := h.prevHash, signature := h.signature, height := h.innerLite.height,
        epochId := h.innerLite.epochId, nextEpochId := h.innerLite.nextEpochId,
        prevStateRoot := h.innerLite.prevStateRoot, prevOutcomeRoot := h.innerLite.prevOutcomeRoot,
        timestamp := h.innerLite.timestamp, nextBpHash := h.innerLite.nextBpHash,
        blockMerkleRoot := h.innerLite.blockMerkleRoot, blockBodyHash := r.blockBodyHash,
        prevChunkOutgoingReceiptsRoot := r.prevChunkOutgoingReceiptsRoot,
        chunkHeadersRoot := r.chunkHeadersRoot, chunkTxRoot := r.chunkTxRoot,
        challengesPresent := !r.challengesResult.isEmpty || r.challengesRoot != CryptoHash.zero,
        randomValue := r.randomValue, prevValidatorProposals := r.prevValidatorProposals,
        chunkMask := r.chunkMask, nextGasPrice := r.nextGasPrice, totalSupply := r.totalSupply,
        lastFinalBlock := r.lastFinalBlock, lastDsFinalBlock := r.lastDsFinalBlock,
        blockOrdinal := r.blockOrdinal, prevHeight := r.prevHeight,
        epochSyncDataHash := r.epochSyncDataHash, approvals := r.approvals,
        latestProtocolVersion := r.latestProtocolVersion,
        chunkEndorsements := some r.chunkEndorsements, shardSplit := none }
  | .v6 h =>
    let r := h.innerRest
    some
      { prevHash := h.prevHash, signature := h.signature, height := h.innerLite.height,
        epochId := h.innerLite.epochId, nextEpochId := h.innerLite.nextEpochId,
        prevStateRoot := h.innerLite.prevStateRoot, prevOutcomeRoot := h.innerLite.prevOutcomeRoot,
        timestamp := h.innerLite.timestamp, nextBpHash := h.innerLite.nextBpHash,
        blockMerkleRoot := h.innerLite.blockMerkleRoot, blockBodyHash := r.blockBodyHash,
        prevChunkOutgoingReceiptsRoot := r.prevChunkOutgoingReceiptsRoot,
        chunkHeadersRoot := r.chunkHeadersRoot, chunkTxRoot := r.chunkTxRoot,
        challengesPresent := false, randomValue := r.randomValue,
        prevValidatorProposals := r.prevValidatorProposals, chunkMask := r.chunkMask,
        nextGasPrice := r.nextGasPrice, totalSupply := r.totalSupply,
        lastFinalBlock := r.lastFinalBlock, lastDsFinalBlock := r.lastDsFinalBlock,
        blockOrdinal := r.blockOrdinal, prevHeight := r.prevHeight,
        epochSyncDataHash := r.epochSyncDataHash, approvals := r.approvals,
        latestProtocolVersion := r.latestProtocolVersion,
        chunkEndorsements := some r.chunkEndorsements, shardSplit := r.shardSplit }
  | _ => none

/-- `BlockHeader::is_genesis`. -/
def HeaderView.isGenesis (h : HeaderView) : Bool :=
  h.prevHash == CryptoHash.zero

end Near.Node

namespace Near.Node.Chain

open Near.Node Borsh

/-- The `Error` variant a check returns (`kind`), with the message of `Error::Other` (`detail`). -/
structure Err where
  kind : String
  detail : String := ""
  deriving BEq, Inhabited, Repr

abbrev Result (α : Type) :=
  Except Err α

/-- An error of the given variant. -/
def fail (kind : String) (detail : String := "") : Result α :=
  .error ⟨kind, detail⟩

/-- `Error::Other(message)`. -/
def failOther (message : String) : Result α :=
  .error ⟨"Other", message⟩

/-- `if c then fail ..`: the guard of a check that returns an error. -/
def guardErr (c : Bool) (kind : String) (detail : String := "") : Result Unit :=
  if c then fail kind detail else pure ()

/-! ### Signatures -/

/-- `near_crypto::Signature::verify`: the scheme of the signature must be the key's. -/
def verifySignature (sig : Signature) (data : ByteArray) (key : PublicKey) : Bool :=
  match sig, key with
  | .ed25519 s, .ed25519 k => NearCrypto.ed25519Verify k data s
  | .secp256k1 s, .secp256k1 k => NearCrypto.secp256k1Verify k data s
  | .mldsa65 s, .mldsa65 k => NearCrypto.mlDsa65Verify k data s
  | _, _ => false

end Near.Node.Chain
