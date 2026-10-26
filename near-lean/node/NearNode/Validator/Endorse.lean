import NearNode.Validator.Node
import NearNode.Validator.Persist

/-!
# Endorsements and state witnesses received

* `send_chunk_endorsement_to_block_producers`: the endorsement of a chunk goes to the block producers of
  the next five heights (without repeats); the node's own is recorded at once.
* `PartialEncodedStateWitness` (`partial_witness_actor.rs`): a part is checked (the epoch is known, the
  node is one of the chunk's validators, the ordinal is in range, the producer signed it) and kept;
  with enough parts the witness is rebuilt (Reed-Solomon, zstd, Borsh), acknowledged to the producer, and
  checked and endorsed once the node has applied the previous block of the chunk.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh
  Near.Node.ReedSolomon

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

/-- `ChunkEndorsementTracker::process_chunk_endorsement` for an endorsement from anyone, ours included. -/
def Env.onEndorsement (e : Env) (en : ChunkEndorsement) : IO Unit := do
  e.bump "ChunkEndorsement"
  let s ← e.get
  let final := (s.st.block (s.st.head)).toOption.map (·.view.lastFinalBlock)
  let finalHeight : BlockHeight :=
    match final with
    | some h => ((s.st.block h).toOption.map (·.view.height)).getD 0
    | none => 0
  match s.tracker.process s.st en s.st.headHeight finalHeight with
  | .ok (t, rel) =>
    e.state.modify fun s => { s with tracker := t }
    if rel != .relevant then
      e.log s!"endorsement of {en.accountId.val} is not relevant: {repr rel}"
  | .error err =>
    e.log s!"endorsement of {en.accountId.val} refused: {err.kind} {err.detail}"

/-- The endorsement of this node for `header`, sent to the next block producers. -/
def Env.endorse (e : Env) (header : ShardChunkHeader) : IO Unit := do
  let s ← e.get
  if s.endorsed.contains header.chunkHash.hash.bytes then
    return
  e.commit #[.set .blockMisc (endorsedKey header.chunkHash.hash.bytes) ByteArray.empty]
  e.state.modify fun s => { s with endorsed := s.endorsed.insert header.chunkHash.hash.bytes }
  match lift (s.st.epochIdFromPrevBlock header.prevBlockHash) with
  | .error m =>
    e.log s!"endorse: {m}"
  | .ok epoch =>
    let en := newChunkEndorsement e.signer epoch header
    for account in endorsementTargets s.st epoch header.heightCreated do
      if account == e.me then
        e.onEndorsement en
      else
        e.toPeer (.versionedChunkEndorsement en)
    e.bump "endorsementsSent"

/-- Starts the replay of a witness on a thread of its own: the chunk validation of a shard whose state the node does not
hold uses nothing but the witness and the chain's headers. -/
def Env.startReplay (e : Env) (w : ChunkStateWitness) : IO Unit := do
  let .v2 v := w
  let s ← e.get
  let re : ReplayEnv :=
    { st := s.st, params := e.params, blockOf := fun h => s.blocks[h.bytes]?,
      genesisExtra := fun shard => s.pr.extras[(s.st.genesisHash.bytes, shard)]?,
      cache := s.pr.cache, validityPeriod := e.validityPeriod, code := e.code }
  let started ← e.nowMs
  let task ← IO.asTask (replayWitness re v).run Task.Priority.dedicated
  e.replays.modify (·.push { witness := w, startedMs := started, task })

/-- Takes up the replays that have finished: a valid witness is endorsed. -/
def Env.pollReplays (e : Env) : IO Unit := do
  let running ← e.replays.get
  if running.isEmpty then
    return
  let mut keep : Array Replaying := #[]
  for r in running do
    unless ← IO.hasFinished r.task do
      keep := keep.push r
      continue
    let .v2 v := r.witness
    let header := v.chunkHeader
    let took := (← e.nowMs) - r.startedMs
    let outcome : Except String Replayed :=
      match r.task.get with
      | .ok o => o
      | .error err => .error s!"the thread failed: {err}"
    match outcome with
    | .ok replayed =>
      e.bump "witnessesValid"
      e.bump "witnessesReplayed"
      e.bumpBy "replayMillis" took
      -- the compiled code the replay decoded stays for the next one
      e.state.modify fun s =>
          { s with
            pr :=
              { s.pr with
                cache :=
                  { s.pr.cache with
                    byLabel :=
                      replayed.cache.byLabel.fold
                        (fun m k x => if m.contains k then m else m.insert k x)
                        s.pr.cache.byLabel } } }
      e.endorse header
    | .error m =>
      e.bump "witnessesInvalid"
      e.log
          s!"state witness of shard {header.shardId} at height {header.heightCreated} refused by replay: {m}"
  e.replays.set keep

/-- The witness, once rebuilt: acknowledged and checked as soon as its previous block is applied. A shard whose state
the node holds is checked against its own execution of the same blocks; every other shard is replayed from the witness. -/
def Env.processWitness (e : Env) (w : ChunkStateWitness) : IO Unit := do
  let .v2 v := w
  let s ← e.get
  let header := v.chunkHeader
  if s.endorsed.contains header.chunkHash.hash.bytes then
    return
  if !s.applied.contains header.prevBlockHash.bytes then
    e.state.modify fun s => { s with waitingWitnesses := s.waitingWitnesses.push w }
    return
  let holds := s.pr.extras.contains (header.prevBlockHash.bytes, header.shardId)
  if holds && !e.replayAll then
    match checkWitness s e.code w with
    | .ok () =>
      e.bump "witnessesValid"
      e.endorse header
    | .error m =>
      e.bump "witnessesInvalid"
      e.log
          s!"state witness of shard {header.shardId} at height {header.heightCreated} refused: {m}"
  else
    if holds then
      -- the node's own execution is the reference: a replay that disagrees is the replay's fault
      match checkWitness s e.code w with
      | .ok () =>
        pure ()
      | .error m =>
        e.log
            s!"state witness of shard {header.shardId} at height {header.heightCreated}: own check: {m}"
    e.startReplay w

/-- A part of a state witness (`handle_partial_encoded_state_witness` and its forward). -/
def Env.onWitnessPart (e : Env) (w : PartialEncodedStateWitness) : IO Unit := do
  e.bump "PartialEncodedStateWitness"
  let s ← e.get
  let key : ChunkProductionKey := ⟨w.inner.shardId, w.inner.epochId, w.inner.heightCreated⟩
  let k := Codec.encode key
  if (s.witnesses[k]?.map (·.done)).getD false then
    return
  let assignments ←
    match lift (s.st.chunkValidatorAssignments key.epochId key.shardId key.heightCreated) with
    | .ok a =>
      pure a
    | .error m =>
      e.log s!"witness part: {m}";
      return
  if !assignments.any (·.1 == e.me) then
    return
  if w.inner.partOrd.toNat ≥ assignments.size then
    e.log "witness part: ordinal out of range"
    return
  let producer ←
    match lift (s.st.chunkProducer key.epochId key.heightCreated key.shardId) with
    | .ok p =>
      pure p
    | .error m =>
      e.log s!"witness part: {m}";
      return
  if !verifySignature w.signature (Codec.encode w.inner) producer.publicKey then
    e.log "witness part: invalid signature"
    return
  let entry := s.witnesses.getD k { key }
  let entry :=
    { entry with
      parts := entry.parts.insert w.inner.partOrd w.inner.part,
      encodedLength := w.inner.encodedLength.toNat }
  let n := assignments.size
  let enc ←
    match Encoder.new n witnessRatio with
    | .ok enc =>
      pure enc
    | .error m =>
      e.log s!"witness part: {m}";
      return
  e.state.modify fun s => { s with witnesses := s.witnesses.insert k entry }
  if entry.parts.size < enc.dataParts then
    return
  -- enough parts: rebuild the compressed witness
  let compressed : Except String ByteArray :=
    match enc.code with
    | some code => do
      let present := (Array.range n).map fun i => entry.parts[i.toUInt64]?
      let bytes ← decodeBytes code present entry.encodedLength
      match Codec.decodeAll (α := EncodedChunkStateWitness) bytes with
      | .ok x =>
        pure x.bytes
      | .error err =>
        throw s!"the encoded witness does not decode: {repr err}"
    | none =>
      match entry.parts[(0 : UInt64)]? with
      | some p => pure p
      | none => throw "the part is missing"
  match compressed with
  | .error m =>
    e.log s!"witness: {m}"
  | .ok z =>
    -- the parts are not needed any more
    e.state.modify fun s =>
        { s with
          witnesses :=
            s.witnesses.insert k
              { entry with
                done := true, parts := {} } }
    match Zstd.decompress z (64 * 1024 * 1024) with
    | .error m =>
      e.log s!"witness: zstd: {m}"
    | .ok raw =>
      match Codec.decodeAll (α := ChunkStateWitness) raw with
      | .error err =>
        e.log s!"witness does not decode: {repr err}"
      | .ok witness =>
        -- the acknowledgement to the chunk producer
        if producer.accountId != e.me then
          e.toPeer (.chunkStateWitnessAck ⟨witness.ack.chunkHash⟩)
        e.bump "witnessesReceived"
        e.processWitness witness

end Near.Node.Validator
