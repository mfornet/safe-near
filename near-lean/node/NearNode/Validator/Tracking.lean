import Lean.Data.Json
import NearNode.Validator.Follow
import NearNode.Chain.ShardTracker

/-!
# What the node applies, and what it needs of the others

A validator applies the shards `ShardTracker::should_apply_chunk` names for the mode the block is in
(`NotCaughtUp` while the state of a shard of the next epoch is being synced, `IsCaughtUp` otherwise) and keeps only
the chunk headers of the others. For a chunk of a shard it does not apply, what an application of its own shards needs
is the receipts the chunk's predecessor sent to them: the receipt proofs of the partial chunk
(`PartialEncodedChunk::prev_outgoing_receipts`, checked against the `prev_outgoing_receipts_root` of the chunk header),
as nearcore's `collect_incoming_receipts_from_chunks` reads them. The bodies are fetched for the shards the node tracks
this epoch or the next (`get_tracking_shards` of the `ShardsManager`).
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh

/-- The shards whose chunk bodies and receipts the node takes for the block after `prev`: those it tracks in the epoch
of that block or the next. -/
def Env.bodyShards (e : Env) (st : CS) (prev : CryptoHash) : Array ShardId :=
  ((e.tracker.shardsThisOrNext st prev).toOption).getD #[]

/-- Whether the blocks of `epoch` are applied without the state of the shards being synced. -/
def VState.syncing (s : VState) (epoch : EpochId) : Bool :=
  s.syncJob.any (·.epoch == epoch)

/-- The mode of the block after `prev` (`get_catchup_and_state_sync_infos`). -/
def Env.applyMode (_e : Env) (s : VState) (prev : CryptoHash) : ApplyMode :=
  match s.st.epochIdFromPrevBlock prev with
  | .ok epoch => if s.syncing epoch then .notCaughtUp else .isCaughtUp
  | .error _ => .isCaughtUp

/-- The shards the chunks of the block after `prev` are applied for. -/
def Env.shardsToApply (e : Env) (s : VState) (prev : CryptoHash) : Array ShardId :=
  ((e.tracker.shardsToApply s.st (e.applyMode s prev) prev).toOption).getD #[]

/-- The receipts the predecessor of the new chunk `c` sent to `targets`, from the proofs the node holds, each checked
against the chunk header's `prev_outgoing_receipts_root`; none when a target has no valid proof. -/
def VState.chunkProofs (s : VState) (c : ShardChunkHeader) (targets : Array ShardId) :
    Option (Array (UInt64 × Array ByteArray)) := do
  let entry ← s.chunks[c.chunkHash.hash.bytes]?
  targets.mapM fun t => do
      let r ←
        entry.receipts.find? fun r =>
            r.proof.toShardId == t && r.proof.fromShardId == c.shardId &&
              r.verifyAgainstReceiptRoot c.prevOutgoingReceiptsRoot
      pure (t, r.receipts.map Codec.encode)

/-- Whether the node applied the chunk before the new chunk `c` of the block with header `v`, and so holds what it
sent. -/
def VState.sentKnown (s : VState) (v : HeaderView) (c : ShardChunkHeader) : Bool :=
  match s.st.block v.prevHash with
  | .ok prevRec =>
    match prevRec.chunks.find? (·.shardId == c.shardId) with
    | some prevChunk =>
      match ancestorAt s.st v.prevHash prevChunk.heightIncluded with
      | .ok included => s.pr.outgoing.contains (included.hash.bytes, c.shardId)
      | .error _ => false
    | none => false
  | .error _ => false

/-- Whether everything the application of `b` reads of its new chunks is in: the bodies of the shards it tracks this or
next epoch, and for every chunk whose predecessor's receipts the node did not compute, the proofs for those shards. -/
def Env.bodiesReady (e : Env) (s : VState) (b : Block) : Bool :=
  match b.header.view? with
  | none => false
  | some v =>
    let shards := e.bodyShards s.st v.prevHash
    (newChunksOf b).all fun c =>
      let bodyOk :=
        !shards.contains c.shardId || ((s.chunks[c.chunkHash.hash.bytes]?).bind (·.body)).isSome
      bodyOk && (s.sentKnown v c || (s.chunkProofs c shards).isSome)

/-- `PartialEncodedChunkRequestMsg` for the parts `ords` and the receipts for `shards`. -/
def chunkRequestFor (h : ShardChunkHeader) (ords : Array UInt64) (shards : Array ShardId) :
    PartialEncodedChunkRequestMsg :=
  { chunkHash := h.chunkHash.hash, partOrds := ords,
    trackingShards := ⟨(shards.qsort (· < ·)).map fun s => (s, ())⟩ }

/-- Asks the peer for what the application of `b` lacks of its new chunks, each at most every 1500 ms: the parts of the
chunks of the shards the node tracks, and the receipts for those shards. -/
def Env.requestBodies (e : Env) (b : Block) : IO Unit := do
  let now ← e.nowMs
  let some v := b.header.view? | return
  for c in newChunksOf b do
    let s ← e.get
    let shards := e.bodyShards s.st v.prevHash
    let entry := s.chunks.getD c.chunkHash.hash.bytes {}
    let needBody := shards.contains c.shardId && entry.body.isNone
    let needProofs := !s.sentKnown v c && (s.chunkProofs c shards).isNone
    if (needBody || needProofs) && (entry.requestedAt == 0 || now - entry.requestedAt ≥ 1500) then
      let ords : Array UInt64 :=
        if needBody then (Array.range e.code.total).map (·.toUInt64) else #[]
      e.toPeer (.partialEncodedChunkRequest (chunkRequestFor c ords shards))
      e.state.modify fun s =>
          s.withChunk c.chunkHash fun x =>
            { x with
              requestedAt := max now 1, header := x.header.orElse fun _ => some c }

/-- One JSON line for an applied block: its hash and, for each shard applied, the transactions, the outcomes and the
state root. -/
def Env.writeAppliedLog (e : Env) (b : Block) (reports : Array ShardReport)
    (bodyOf : UInt64 → Body) : IO Unit := do
  let some v := b.header.view? | return
  let hash := b.header.hash
  if let some h := e.appliedLog then
    let hex (b : ByteArray) : String :=
      b.foldl (fun s x => s ++ String.ofList (Nat.toDigits 16 (x.toNat + 256)).tail) ""
    let outcomeJson (o : ExecutionOutcomeWithId) : Lean.Json :=
      Lean.Json.mkObj
        [("id", Lean.Json.str (hex o.id.bytes)),
          ("executor", Lean.Json.str o.outcome.executorId.val),
          ("gasBurnt", Lean.Json.num (Lean.JsonNumber.fromNat o.outcome.gasBurnt.toNat)),
          ("tokensBurnt", Lean.Json.str (toString o.outcome.tokensBurnt.val)),
          ("status",
            Lean.Json.str
              (match o.outcome.status with
              | .successValue v => s!"value:{hex v}"
              | .successReceiptId r => s!"receipt:{hex r.bytes}"
              | .failure _ => "failure"
              | .unknown => "unknown")),
          ("receipts",
            Lean.Json.arr (o.outcome.receiptIds.map fun r => Lean.Json.str (hex r.bytes)))]
    let chunks :=
      reports.toList.map fun r =>
        let isNew := (b.chunks.find? (·.shardId == r.shard)).any (·.isNewChunk v.height)
        let txs :=
          if isNew then (bodyOf r.shard).transactions.map fun t => Lean.Json.str (hex t.hash.bytes)
          else #[]
        let base : List (String × Lean.Json) :=
          [("shard", Lean.Json.num (Lean.JsonNumber.fromNat r.shard.toNat)),
            ("txs", Lean.Json.arr txs), ("outcomes", Lean.Json.arr (r.outcomes.map outcomeJson))]
        match r.extra with
        | .v5 x =>
          Lean.Json.mkObj
            (base ++
              [("stateRoot", Lean.Json.str (hex x.stateRoot.bytes)),
                ("gasUsed", Lean.Json.num (Lean.JsonNumber.fromNat x.gasUsed.toNat))])
        | _ => Lean.Json.mkObj base
    h.putStrLn
        (Lean.Json.mkObj
            [("height", Lean.Json.num (Lean.JsonNumber.fromNat v.height.toNat)),
              ("hash", Lean.Json.str (hex hash.bytes)),
              ("chunks", Lean.Json.arr chunks.toArray)]).compress
    h.flush

end Near.Node.Validator
