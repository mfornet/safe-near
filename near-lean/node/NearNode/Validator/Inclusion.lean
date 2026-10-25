import NearNode.Chain.State
import NearNode.Validator.Doomslug

/-!
# Chunk endorsements and the chunks a block includes

* **Endorsements** (`chunk_endorsement.rs`, `validate.rs`, `validator_assignment.rs`). A
  `ChunkEndorsement` is kept when its chunk is relevant (above the final head, at most five heights above
  the head, a known epoch and shard), the sender is one of the chunk's validators and both signatures
  verify under the validator's key. `compute_endorsement_state` sums the stake of the validators of the
  chunk that endorsed its hash and says whether it exceeds two thirds (`total * 2 / 3 + 1`); the
  signatures come out in assignment order, empty if the chunk is not endorsed.
* **Inclusion** (`chunk_inclusion_tracker.rs`). A chunk that the node produced or received completely is
  *ready*; one with enough endorsements is *included* in the block on top of its previous block. The
  chunks are ready (`ChunksReadiness`) when every shard has one.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Borsh

/-- `ChunkEndorsementsState`. -/
structure EndorsementState where
  totalStake : Nat := 0
  endorsedStake : Nat := 0
  endorsedCount : Nat := 0
  totalCount : Nat := 0
  isEndorsed : Bool := false
  signatures : Array (Option Signature) := #[]
  deriving Inhabited

/-- `required_stake`. -/
def requiredStake (total : Nat) : Nat :=
  total * 2 / 3 + 1

/-- `ChunkValidatorAssignments::compute_endorsement_state`. -/
def endorsementState (assignments : Array (AccountId × Balance))
    (signatures : Std.HashMap String Signature) : EndorsementState :=
  Id.run do
    let mut s : EndorsementState := { totalCount := assignments.size }
    let mut sigs : Array (Option Signature) := #[]
    for (account, stake) in assignments do
      s := { s with totalStake := s.totalStake + stake.val }
      match signatures[account.val]? with
      | some sig =>
        s :=
          { s with
            endorsedStake := s.endorsedStake + stake.val, endorsedCount := s.endorsedCount + 1 }
        sigs := sigs.push (some sig)
      | none =>
        sigs := sigs.push none
    let isEndorsed := s.endorsedStake ≥ requiredStake s.totalStake
    return { s with
        isEndorsed, signatures := if isEndorsed then sigs else #[] }

/-- `ChunkRelevance`. -/
inductive Relevance where
  | relevant
  | tooLate
  | tooEarly
  | unknownEpochId
  deriving BEq, Repr

/-- `MAX_HEIGHTS_AHEAD` of `validate.rs`. -/
def maxHeightsAhead : UInt64 :=
  5

/-- `validate_chunk_relevant`: the shard is in the epoch's layout, the height is above the final head and
at most `maxHeightsAhead` above the head. The epoch must be known; nearcore also checks it is among
the epochs possible for the height, which for a chain that follows one head means the head's, or the
next one's near a boundary: the epochs the state knows. -/
def chunkRelevant (st : ChainState) (key : ChunkProductionKey)
    (headHeight finalHeight : BlockHeight) : Result Relevance := do
  let e ← st.epoch key.epochId
  unless e.layout.shardIds.contains key.shardId do
    fail "InvalidShardId" s!"{key.shardId}"
  if key.heightCreated ≤ finalHeight then
    return .tooLate
  if key.heightCreated > headHeight + maxHeightsAhead then
    return .tooEarly
  return .relevant

/-- `ensure_chunk_validator`. -/
def isChunkValidator (st : ChainState) (key : ChunkProductionKey) (account : AccountId) :
    Result Bool := do
  let assignments ← st.chunkValidatorAssignments key.epochId key.shardId key.heightCreated
  pure (assignments.any (·.1 == account))

/-- `ChunkEndorsement::verify`: both signatures under the validator's key. -/
def verifyEndorsement (e : ChunkEndorsement) (key : PublicKey) : Bool :=
  verifySignature
      (match e with
      | .v2 x => x.signature)
      e.signingBytes key &&
    verifySignature
      (match e with
      | .v2 x => x.metadataSignature)
      e.metadataSigningBytes key

def _root_.Near.Node.ChunkEndorsement.accountId : ChunkEndorsement → AccountId
  | .v2 e => e.metadata.accountId

def _root_.Near.Node.ChunkEndorsement.signature : ChunkEndorsement → Signature
  | .v2 e => e.signature

/-- `ChunkEndorsementTracker`: the validated endorsements by chunk production key. -/
structure EndorsementTracker where
  entries : Std.HashMap ByteArray (Array (AccountId × ChunkHash × Signature)) := {}
  deriving Inhabited

/-- `validate_chunk_endorsement` followed by `process_chunk_endorsement`'s insertion. -/
def EndorsementTracker.process (t : EndorsementTracker) (st : ChainState) (e : ChunkEndorsement)
    (headHeight finalHeight : BlockHeight) : Result (EndorsementTracker × Relevance) := do
  let key := e.chunkProductionKey
  let account := e.accountId
  let k := Codec.encode key
  if (t.entries[k]?.getD #[]).any (·.1 == account) then
    return (t, .relevant)
  let rel ← chunkRelevant st key headHeight finalHeight
  if rel != .relevant then
    return (t, rel)
  unless ← isChunkValidator st key account do
    fail "NotAChunkValidator" account.val
  let validator ← st.validatorByAccount key.epochId account
  unless verifyEndorsement e validator.publicKey do
    fail "InvalidChunkEndorsement"
  return ({ t with
        entries :=
          t.entries.insert k ((t.entries[k]?.getD #[]).push (account, e.chunkHash, e.signature)) },
      .relevant)

/-- `collect_chunk_endorsements`: the state of the endorsements of a chunk header. -/
def EndorsementTracker.collect (t : EndorsementTracker) (st : ChainState)
    (header : ShardChunkHeader) : Result EndorsementState := do
  let epoch ← st.epochIdFromPrevBlock header.prevBlockHash
  let key : ChunkProductionKey := ⟨header.shardId, epoch, header.heightCreated⟩
  let assignments ← st.chunkValidatorAssignments epoch header.shardId header.heightCreated
  let sigs : Std.HashMap String Signature :=
    (t.entries[Codec.encode key]?.getD #[]).foldl
      (fun m (a, h, s) => if h == header.chunkHash then m.insert a.val s else m) {}
  pure (endorsementState assignments sigs)

/-- A chunk ready to be included. -/
structure ChunkInfo where
  header : ShardChunkHeader
  producer : AccountId
  receivedAt : Nat
  endorsements : EndorsementState := {}
  deriving Inhabited

/-- `ChunkInclusionTracker`. -/
structure Inclusion where
  /-- The chunks ready on top of a block, by shard. -/
  ready : Std.HashMap ByteArray (Array (ShardId × ChunkHash)) := {}
  info : Std.HashMap ByteArray ChunkInfo := {}
  readyAt : Std.HashMap ByteArray Nat := {}
  banned : Array (EpochId × AccountId) := #[]
  deriving Inhabited

/-- `mark_chunk_header_ready_for_inclusion`. -/
def Inclusion.markReady (i : Inclusion) (header : ShardChunkHeader) (producer : AccountId)
    (now : Nat) : Inclusion :=
  let prev := header.prevBlockHash.bytes
  let hash := header.chunkHash
  let shard := header.shardId
  let entry := ((i.ready[prev]?.getD #[]).filter (·.1 != shard)).push (shard, hash)
  { i with
    ready := i.ready.insert prev entry,
    info := i.info.insert hash.hash.bytes { header, producer, receivedAt := now } }

/-- `prepare_chunk_headers_ready_for_inclusion`: refreshes the endorsements of the chunks on `prev`. -/
def Inclusion.prepare (i : Inclusion) (t : EndorsementTracker) (st : ChainState)
    (prev : CryptoHash) : Result Inclusion := do
  let mut i := i
  for (_, h) in i.ready[prev.bytes]?.getD #[] do
    if let some info := i.info[h.hash.bytes]? then
      i :=
        { i with
          info :=
            i.info.insert h.hash.bytes { info with endorsements := ← t.collect st info.header } }
  pure i

/-- `get_chunk_headers_ready_for_inclusion`: the chunks on `prev` that are endorsed and not banned. -/
def Inclusion.readyForInclusion (i : Inclusion) (epoch : EpochId) (prev : CryptoHash) :
    Array (ShardId × ChunkHash) :=
  (i.ready[prev.bytes]?.getD #[]).filter fun (_, h) =>
    match i.info[h.hash.bytes]? with
    | some info =>
      info.endorsements.isEndorsed && !i.banned.any (fun (e, a) => e == epoch && a == info.producer)
    | none => false

/-- `get_chunks_readiness`: ready once every shard has an included chunk (the time is kept). -/
def Inclusion.readiness (i : Inclusion) (now : Nat) (epoch : EpochId) (prev : CryptoHash)
    (numShards : Nat) : Inclusion × ChunksReadiness :=
  match i.readyAt[prev.bytes]? with
  | some t => (i, .ready t)
  | none =>
    if (i.readyForInclusion epoch prev).size == numShards then
      ({ i with readyAt := i.readyAt.insert prev.bytes now }, .ready now)
    else (i, .notReady)

/-- `get_chunk_header_and_endorsements`. -/
def Inclusion.headerAndEndorsements (i : Inclusion) (h : ChunkHash) :
    Option (ShardChunkHeader × Array (Option Signature)) :=
  (i.info[h.hash.bytes]?).map fun x => (x.header, x.endorsements.signatures)

end Near.Node.Validator
