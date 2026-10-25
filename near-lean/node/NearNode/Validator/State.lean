import NearNode.Network.Chunks
import NearNode.Chain.Apply
import NearNode.Validator.Inclusion
import NearNode.Validator.Produce
import NearNode.Validator.Chunk
import NearNode.Validator.ReedSolomon
import NearNode.Validator.Pool

/-!
# The state of a running validator

The data the validator keeps while it follows and produces a chain, and the pure functions on it:
which chunks of the store are complete, who owns a part of a chunk, which blocks can be applied.
-/

namespace Near.Node.Validator

abbrev CS :=
  Near.Node.Chain.ChainState

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh
  Near.Node.ReedSolomon

/-- A chunk as the node assembles it from parts. -/
structure ChunkEntry where
  header : Option ShardChunkHeader := none
  parts : Std.HashMap UInt64 PartialEncodedChunkPart := {}
  receipts : Array ReceiptProof := #[]
  body : Option TransactionReceipt := none
  /-- When the parts were last requested, in milliseconds. -/
  requestedAt : Nat := 0
  /-- Whether a header was checked against the chunk producer. -/
  verified : Bool := false
  /-- Parts that came before the header, checked when it arrives. -/
  pendingParts : Array PartialEncodedChunkPart := #[]
  deriving Inhabited

/-- A state witness being collected: its parts by ordinal. -/
structure WitnessEntry where
  key : ChunkProductionKey
  parts : Std.HashMap UInt64 ByteArray := {}
  encodedLength : Nat := 0
  header : Option ShardChunkHeader := none
  done : Bool := false
  deriving Inhabited

/-- An execution outcome as the store keeps it (`ExecutionOutcomeWithProof` and the block it was produced
in): the path of its leaf in the outcome tree of the shard's chunk. -/
structure OutcomeRec where
  block : CryptoHash
  shard : UInt64
  proof : Array MerklePathItem
  outcome : ExecutionOutcomeWithId
  deriving Inhabited

/-- Everything the validator keeps. -/
structure VState where
  st : CS
  pr : Progress
  /-- The accepted blocks by hash. -/
  blocks : Std.HashMap ByteArray Block := {}
  /-- Accepted blocks that are not applied yet. -/
  pending : Array CryptoHash := #[]
  /-- The blocks that are applied, by hash, with their height. -/
  applied : Std.HashMap ByteArray BlockHeight := {}
  /-- The applied block that is the head of the chain, as the doomslug tip. -/
  tip : CryptoHash
  tipHeight : BlockHeight
  /-- Blocks whose parent is not known, by the hash of the parent. -/
  orphans : Std.HashMap ByteArray (Array Block) := {}
  chunks : Std.HashMap ByteArray ChunkEntry := {}
  /-- The receipts a chunk applied at a block and shard, as applied, in order. -/
  deliveredAt : Std.HashMap (ByteArray × UInt64) (Array ByteArray) := {}
  /-- The bodies of chunks that were included, by chunk hash. -/
  bodies : Std.HashMap ByteArray TransactionReceipt := {}
  ds : Doomslug
  tracker : EndorsementTracker := {}
  inclusion : Inclusion := {}
  /-- The greatest height of a block the node knows or produced (`latest_known`). -/
  latestKnown : BlockHeight := 0
  witnesses : Std.HashMap ByteArray WitnessEntry := {}
  /-- Witnesses waiting for their previous block to be applied. -/
  waitingWitnesses : Array ChunkStateWitness := #[]
  endorsed : Std.HashSet ByteArray := {}
  producedChunks : Std.HashSet (UInt64 × UInt64) := {}
  /-- Approvals whose parent block is not known yet. -/
  parkedApprovals : Array Approval := #[]
  /-- The applied blocks of the chain of the tip, by height. -/
  canon : Std.HashMap UInt64 ByteArray := {}
  /-- Execution outcomes by transaction hash or receipt id. -/
  outcomes : Std.HashMap ByteArray OutcomeRec := {}
  /-- The applied transactions by hash: the block and the chunk that included them. -/
  txIndex : Std.HashMap ByteArray (CryptoHash × ChunkHash) := {}
  /-- The receipts of the chunks applied, by receipt id (`DBCol::Receipts`). -/
  receiptsById : Std.HashMap ByteArray Receipt := {}
  /-- Epochs the accepted blocks finalized, until the block is applied and stored. -/
  finalized : Std.HashMap ByteArray Epoch.Finalized := {}
  /-- The transaction pool of each shard the node produces chunks for. -/
  pools : Std.HashMap UInt64 Pool := {}
  /-- Counters for the report. -/
  stats : Std.HashMap String Nat := {}

/-- The height index after `hash` at `height` became the tip: the heights above are dropped and the
chain is followed back until it meets the index again. -/
def VState.canonWith (s : VState) (hash : CryptoHash) (height : BlockHeight) :
    Std.HashMap UInt64 ByteArray :=
  Id.run do
    let mut canon := s.canon
    -- a block that is not above the old tip replaced a fork
    if height ≤ s.tipHeight then
      for h in [height.toNat:s.tipHeight.toNat + 1] do
        canon := canon.erase h.toUInt64
    let mut cur := hash
    let mut h := height
    for _ in [0:100000] do
      if canon[h]? == some cur.bytes then
        break
      canon := canon.insert h cur.bytes
      match s.st.block cur with
      | .ok r =>
        if h == 0 || r.view.prevHash == CryptoHash.zero then
          break
        cur := r.view.prevHash
        h := r.view.prevHeight
      | .error _ =>
        break
    return canon

def VState.bump (s : VState) (name : String) : VState :=
  { s with stats := s.stats.insert name (s.stats.getD name 0 + 1) }

/-- `get_part_owner`: the block producer seat `ord % seats` of the epoch. -/
def partOwner (st : CS) (epoch : EpochId) (ord : Nat) : Result AccountId := do
  let settlement ← st.blockProducersSettlement epoch
  if settlement.isEmpty then
    fail "ValidatorError" "no block producers"
  pure settlement[ord % settlement.size]!.accountId

/-- The chunk validators of the chunk that follows `prev` for `shard`, in assignment order. -/
def chunkValidatorsOf (st : CS) (prev : CryptoHash) (shard : ShardId) (height : BlockHeight) :
    Result (EpochId × Array (AccountId × Balance)) := do
  let epoch ← st.epochIdFromPrevBlock prev
  pure (epoch, ← st.chunkValidatorAssignments epoch shard height)

/-- The block producers of the heights `height .. height + 4` (the account that gets an endorsement
of a chunk created at `height`), without repeats. -/
def endorsementTargets (st : CS) (epoch : EpochId) (height : BlockHeight) : Array AccountId :=
  Id.run do
    let mut out : Array AccountId := #[]
    for i in [0:5] do
      match st.blockProducer epoch (height + i.toUInt64) with
      | .ok v =>
        if !out.contains v.accountId then
          out := out.push v.accountId
      | .error _ =>
        break
    return out

/-- The block at `height` on the chain that ends at `from`. -/
def ancestorAt (st : CS) (fromHash : CryptoHash) (height : BlockHeight) : Result BlockRec := do
  let mut cur ← st.block fromHash
  for _ in [0:1000000] do
    if cur.view.height == height then
      return cur
    if cur.view.height < height then
      break
    cur ← st.block cur.view.prevHash
  fail "DBNotFoundErr" s!"no block at height {height}"

/-- The encoded length of a chunk and the code of its parts. -/
def chunkCode (total : Nat) : Except String Code :=
  Code.new (Network.numDataParts total) (total - Network.numDataParts total)

/-- Rebuilds the body of a chunk from the parts present: reconstructs the missing data parts. -/
def assembleBody (code : Code) (h : ShardChunkHeader)
    (parts : Std.HashMap UInt64 PartialEncodedChunkPart) : Except String TransactionReceipt := do
  let total := code.total
  let present : Array (Option ByteArray) :=
    (Array.range total).map fun i => (parts[i.toUInt64]?).map (·.part)
  let len := h.encodedLength.toNat
  let bytes ← decodeBytes code present len
  match Codec.decodeAll (α := TransactionReceipt) bytes with
  | .ok b =>
    pure b
  | .error e =>
    throw s!"the chunk body does not decode: {repr e}"

/-- `validate_chunk_with_encoded_merkle_root`: the body re-encoded gives the header's root and length. -/
def checkEncoding (code : Code) (h : ShardChunkHeader) (body : TransactionReceipt) : Bool :=
  match encodeBytes code (Codec.encode body) with
  | .ok (parts, len) =>
    let (root, _) := merklize parts
    root == h.encodedMerkleRoot && len.toUInt64 == h.encodedLength
  | .error _ => false

end Near.Node.Validator
