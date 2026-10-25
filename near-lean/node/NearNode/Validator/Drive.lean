import Lean.Data.Json
import NearNode.Validator.Follow
import NearNode.Validator.Gc
import NearNode.Validator.Persist

/-!
# Driving the validator

The loop body of a validator: blocks in, blocks applied, approvals out, blocks produced, and the
dispatch of everything the peer sends.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh
  Near.Node.ReedSolomon

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

/-! ### Applying blocks -/

/-- Whether the bodies of all new chunks of `b` are in. -/
def VState.bodiesReady (s : VState) (b : Block) : Bool :=
  (newChunksOf b).all fun c => ((s.chunks[c.chunkHash.hash.bytes]?).bind (·.body)).isSome

/-- Asks the peer for the chunks of `b` whose bodies are missing, at most every 1500 ms each. -/
def Env.requestBodies (e : Env) (b : Block) : IO Unit := do
  let now ← e.nowMs
  for c in newChunksOf b do
    let s ← e.get
    let entry := s.chunks.getD c.chunkHash.hash.bytes {}
    if entry.body.isNone && (entry.requestedAt == 0 || now - entry.requestedAt ≥ 1500) then
      e.toPeer (.partialEncodedChunkRequest (chunkRequest c e.code.total))
      e.state.modify fun s =>
          s.withChunk c.chunkHash fun x =>
            { x with
              requestedAt := max now 1, header := x.header.orElse fun _ => some c }

/-- The state roots of a block's parent, which the application starts from. -/
def rootsOf (s : VState) (layout : ShardLayout) (parent : CryptoHash) :
    Std.HashMap UInt64 CryptoHash :=
  layout.shardIds.foldl
    (fun m shard =>
      match s.pr.extras[(parent.bytes, shard)]? with
      | some (ChunkExtra.v5 x) => m.insert shard x.stateRoot
      | _ => m)
    {}

/-- The body of a chunk as the application gets it: its transactions (the receipts it claims are not known to a
node that applies at the head). -/
private def emptyBody : Body :=
  { transactions := #[], claimedOutgoing := #[], claimedIncoming := #[] }

/-- Starts to apply `b`, its chunks on the state its parent left, on a thread of its own (nearcore applies chunks in
a pool apart from the client actor: `ApplyChunksIterationMode`, `apply_chunks_spawner`). The application reads a
snapshot of the chain state and of the progress, and writes nothing: what it computes is taken up by `finishApply`
on the event loop, so everything else the node does (answering the peer, collecting approvals, serving the RPC,
forwarding parts, the Doomslug timers) goes on, and nothing is produced on a block that is not applied, because the
tip only moves when `finishApply` and `onApplied` run. Returns false when it cannot start. -/
def Env.startApply (e : Env) (b : Block) : IO Bool := do
  let s ← e.get
  let some v := b.header.view? | return false
  let started ← IO.monoMsNow
  let layoutE : Except String ShardLayout := do
    let epoch ← lift (s.st.epochIdFromPrevBlock v.prevHash)
    pure (← lift (s.st.epoch epoch)).layout
  match layoutE with
  | .error m =>
    e.failure.modify fun f => f.orElse fun _ => some s!"block {v.height}: {m}"
    return false
  | .ok layout =>
    let pr0 := { s.pr with roots := rootsOf s layout v.prevHash }
    let bodies : Std.HashMap UInt64 Body :=
      b.chunks.foldl
        (fun m c =>
          match (s.chunks[c.chunkHash.hash.bytes]?).bind (·.body) with
          | some body => m.insert c.shardId { emptyBody with transactions := body.transactions }
          | none => m)
        {}
    let params := e.params
    let st := s.st
    let task ←
      IO.asTask ((applyBlock none params st b (fun shard => bodies.getD shard emptyBody) pr0).run)
          Task.Priority.dedicated
    e.applying.set (some { block := b, bodies, startedMs := started, task })
    return true

/-- Takes up a block whose application has finished: the progress and the store operations. -/
def Env.finishApply (e : Env) (a : Applying) : IO Bool := do
  let b := a.block
  let some v := b.header.view? | return false
  let hash := b.header.hash
  let bodyOf (shard : UInt64) : Body := a.bodies.getD shard emptyBody
  let applied ←
    match a.task.get with
    | .ok r =>
      pure r
    | .error err =>
      pure (.error s!"the thread failed: {err}")
  match applied with
  | .error m =>
    e.failure.modify fun f =>
        f.orElse fun _ => some s!"block {v.height}: applying the chunks failed: {m}"
    return false
  | .ok (pr, reports, chunkOps) =>
    e.state.modify fun s =>
        let delivered :=
          reports.foldl (fun m r => m.insert (hash.bytes, r.shard) r.incoming) s.deliveredAt
        { s with
          pr, applied := s.applied.insert hash.bytes v.height,
          pending := s.pending.filter (· != hash), deliveredAt := delivered }
    e.bump "blocksApplied"
    -- the block, its chunks and what the RPC serves of it go to the store in one commit
    let s1 ← e.get
    let (extraOps, s2) := appliedOps s1 b reports
    match commitOps s1.st b (s1.finalized[hash.bytes]?) chunkOps with
    | .ok ops =>
      e.commit (ops ++ extraOps)
    | .error m =>
      e.failure.modify fun f => f.orElse fun _ => some s!"block {v.height}: {m}"
    e.state.modify fun s =>
        { s with
          outcomes := s2.outcomes, txIndex := s2.txIndex, receiptsById := s2.receiptsById,
          finalized := s.finalized.erase hash.bytes }
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
            if isNew then
              (bodyOf r.shard).transactions.map fun t => Lean.Json.str (hex t.hash.bytes)
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
    let took := (← IO.monoMsNow) - a.startedMs
    if took > 400 then
      e.log s!"block {v.height} took {took} ms to apply"
    e.state.modify fun s =>
        s.bump s!"applyMillis" |>.bump "applyMillisTotal" |> fun s =>
          { s with
            stats :=
              s.stats.insert "applyMillisTotal" (s.stats.getD "applyMillisTotal" 0 + took - 1) }
    return true

/-- The transactions of the chunks a block includes leave the pools (`remove_transactions` when a block is
accepted). -/
def Env.dropIncluded (e : Env) (b : Block) : IO Unit := do
  let some v := b.header.view? | return
  for c in b.chunks do
    if c.isNewChunk v.height then
      let s ← e.get
      if let some body := s.bodies[c.chunkHash.hash.bytes]? then
        if let some pool := s.pools[c.shardId]? then
          e.state.modify fun s =>
              { s with pools := s.pools.insert c.shardId (pool.remove body.transactions) }

/-- After a block is applied: the Doomslug tip, the chunks to produce, the witnesses that waited. -/
def Env.onApplied (e : Env) (b : Block) : IO Unit := do
  let s ← e.get
  let some v := b.header.view? | return
  let hash := b.header.hash
  if v.height % 100 == 0 then
    e.log s.census
    if let some store := e.store then
      let t ← store.tables.get
      let cols :=
        (List.range t.plain.size).filterMap fun i =>
          if t.plain[i]!.size == 0 then none else some s!"{i}:{t.plain[i]!.size}"
      e.log s!"census of the store: trie {t.rc.size} entries; columns {cols}"
  if v.height > s.tipHeight then
    let lastFinal : BlockHeight :=
      if v.lastFinalBlock == CryptoHash.zero then s.st.config.genesisHeight
      else ((s.st.block v.lastFinalBlock).toOption.map (·.view.height)).getD 0
    let now ← e.nowMs
    e.state.modify fun s =>
        { s with
          ds := s.ds.setTip hash v.height lastFinal now, tip := hash, tipHeight := v.height,
          canon := s.canonWith hash v.height }
    e.produceChunks b
  e.dropIncluded b
  let s ← e.get
  let (ready, waiting) :=
    s.waitingWitnesses.partition fun w =>
      match w with
      | .v2 x => s.applied.contains x.chunkHeader.prevBlockHash.bytes
  e.state.modify fun s => { s with waitingWitnesses := waiting }
  for w in ready do
    e.processWitness w

/-- Applies the blocks that can be applied, one after the other (a block is applied on the state its parent left).
A block starts on a thread of its own (`startApply`) and is taken up here once the thread is done: this is called on
every turn of the loop, so a finished block is noticed within a turn and the next one starts at once. -/
partial def Env.tryApply (e : Env) : IO Unit := do
  if (← e.failure.get).isSome then
    return
  if let some a← e.applying.get then
    unless ← IO.hasFinished a.task do
      return
    e.applying.set none
    if ← e.finishApply a then
      e.onApplied a.block
      -- between two applications: the next one starts on the state this leaves
      e.collectGarbage
    else
      return
  let s ← e.get
  let candidates :=
    s.pending.filterMap fun h => (s.blocks[h.bytes]?).bind fun b => b.header.view?.map (b, ·.height)
  let sorted := candidates.qsort fun a b => a.2 < b.2
  for (b, _) in sorted do
    let some v := b.header.view? | continue
    if s.applied.contains v.prevHash.bytes then
      if s.bodiesReady b then
        discard <| e.startApply b
        return
      else
        e.requestBodies b

/-! ### Receiving blocks -/

/-- Validates a block from the peer or produced here, records it, and applies what can be applied. -/
partial def Env.ingestBlock (e : Env) (b : Block) : IO Unit := do
  let s ← e.get
  let h := b.header.hash
  let some v := b.header.view? | return
  if s.blocks.contains h.bytes then
    return
  e.bump "BlockReceived"
  match Epoch.processBlock e.setup s.st b with
  | .error err =>
    if err.kind == "Orphan" || err.kind == "DBNotFoundErr" then
      e.state.modify fun s =>
          let old := s.orphans.getD v.prevHash.bytes #[]
          if old.any (·.header.hash == h) then s
          else { s with orphans := s.orphans.insert v.prevHash.bytes (old.push b) }
      e.outbox.modify (·.push (.blockRequest v.prevHash))
      e.bump "BlockOrphan"
    else
      e.bump "BlockRejected"
      e.log s!"block {v.height} rejected: {err.kind} {err.detail}"
  | .ok (st', fin) =>
    if let some f := fin then
      let kicked :=
        f.data.info.view.validatorKickout.map fun (a, r) =>
          s!"{a.val}: {match r with | .notEnoughBlocks p x => s!"blocks {p}/{x}" | .notEnoughChunks p x => s!"chunks {p}/{x}" | .notEnoughChunkEndorsements p x => s!"endorsements {p}/{x}" | .notEnoughStake _ _ => "stake" | .unstaked => "unstaked" | .didNotGetASeat => "no seat" | _ => "other"}"
      e.log
          s!"epoch finalized at block {v.height}: validators {f.data.info.view.validators.map (·.accountId.val)}, kicked out {kicked}"
      e.log
          s!"epoch stats {f.summary.stats.map fun (a, t) => s!"{a.val} blocks {t.blockProduced}/{t.blockExpected} chunks {t.chunkProduced}/{t.chunkExpected} endorsements {t.endorsementProduced}/{t.endorsementExpected}"}; stakes {f.data.info.view.validators.map fun v => s!"{v.accountId.val}={v.stake.val}"}"
    e.state.modify fun s =>
        { s with
          st := st', blocks := s.blocks.insert h.bytes b, pending := s.pending.push h,
          latestKnown := max s.latestKnown v.height,
          finalized :=
            match fin with
            | some f => s.finalized.insert h.bytes f
            | none => s.finalized }
    for c in newChunksOf b do
      e.noteHeader c
      e.state.modify fun s => s.withChunk c.chunkHash fun x => { x with verified := true }
    -- chunks that came before their previous block
    let s ← e.get
    for (_, entry) in s.chunks.toList do
      if let some ch := entry.header then
        if ch.prevBlockHash == h then
          discard <| e.refreshChunk ch.chunkHash
    -- children that waited for this block
    let children := (← e.get).orphans.getD h.bytes #[]
    e.state.modify fun s => { s with orphans := s.orphans.erase h.bytes }
    for c in children do
      e.ingestBlock c
    e.tryApply

/-! ### Approvals -/

/-- `resolve_skip_parent`: the block at `parent_height` on the chain of the head. -/
def Env.skipParent (e : Env) (parentHeight : BlockHeight) : IO (Option CryptoHash) := do
  let s ← e.get
  pure ((ancestorAt s.st s.st.head parentHeight).toOption.map (·.hash))

/-- `Client::collect_block_approval`. -/
def Env.collectApproval (e : Env) (a : Approval) (fromPeer : Bool) : IO Unit := do
  let s ← e.get
  let parent? ←
    match a.inner with
    | .endorsement h =>
      pure (some h)
    | .skip ph =>
      e.skipParent ph
  let some parent := parent? |
    e.state.modify (fun s => { s with parkedApprovals := s.parkedApprovals.push a });
    return
  if !s.st.blockExists parent then
    e.state.modify fun s => { s with parkedApprovals := s.parkedApprovals.push a }
    return
  let r : Except String (Option (Array ApprovalStake)) := do
    let nextEpoch ← lift (s.st.epochIdFromPrevBlock parent)
    if fromPeer then
      let validatorEpoch ←
        match s.st.validatorByAccount nextEpoch a.accountId with
        | .ok _ =>
          pure nextEpoch
        | .error _ =>
          lift (s.st.nextEpochIdFromPrevBlock parent)
      let v ← lift (s.st.validatorByAccount validatorEpoch a.accountId)
      unless
        verifySignature a.signature (Approval.getDataForSig a.inner a.targetHeight) v.publicKey do
        throw "invalid approval signature"
    let producer ← lift (s.st.blockProducer nextEpoch a.targetHeight)
    if producer.accountId != e.me then
      return none
    let next ← lift (s.st.nextEpochIdFromPrevBlock parent)
    some <$> lift (s.st.blockApprovers parent nextEpoch next)
  match r with
  | .error m =>
    e.log s!"approval of {a.accountId.val} for {a.targetHeight} refused: {m}"
  | .ok none =>
    pure ()
  | .ok (some stakes) =>
    let now ← e.nowMs
    e.state.modify fun s => { s with ds := s.ds.onApproval a stakes now }
    e.bump "approvalsCollected"

/-- `Client::send_block_approval`: to the producer of the target height. -/
def Env.sendApproval (e : Env) (a : Approval) : IO Unit := do
  let s ← e.get
  match lift (s.st.epochIdFromPrevBlock s.tip) with
  | .error m =>
    e.log s!"approval: {m}"
  | .ok epoch =>
    let mut targets : Array AccountId := #[]
    -- a skip may need the producer of the previous epoch too, while the epoch change is not final
    match a.inner with
    | .skip _ =>
      let finalEpoch :=
        (s.st.block s.tip).toOption.bind fun r =>
          (s.st.block r.view.lastFinalBlock).toOption.map (·.info.epochId)
      if let some fe := finalEpoch then
        if fe != epoch then
          if let .ok p := s.st.blockProducer fe a.targetHeight then
            targets := targets.push p.accountId
    | _ =>
      pure ()
    match s.st.blockProducer epoch a.targetHeight with
    | .ok p =>
      targets := targets.push p.accountId
    | .error _ =>
      pure ()
    for t in targets do
      if t == e.me then
        e.collectApproval a false
      else
        e.toPeer (.blockApproval a)
    e.bump "approvalsSent"

/-- Approvals that waited for a block. -/
def Env.retryParked (e : Env) : IO Unit := do
  let s ← e.get
  if s.parkedApprovals.isEmpty then
    return
  e.state.modify fun s => { s with parkedApprovals := #[] }
  for a in s.parkedApprovals do
    -- too old to matter once the tip is past its target
    if a.targetHeight ≥ s.tipHeight then
      e.collectApproval a true

/-! ### Producing blocks -/

/-- `Client::produce_block`, once Doomslug says the block for `height` is ready. -/
def Env.produceBlock (e : Env) (height : BlockHeight) : IO Unit := do
  let s ← e.get
  match lift (s.st.epochIdFromPrevBlock s.tip) with
  | .error m =>
    e.log s!"produce block: {m}"
  | .ok epoch =>
    let chosen := s.inclusion.readyForInclusion epoch s.tip
    let newChunks : Array (ShardId × NewChunk) :=
      chosen.filterMap fun (shard, h) =>
        (s.inclusion.headerAndEndorsements h).map fun (header, sigs) => (shard, ⟨header, sigs⟩)
    let approvals := (s.ds.witness s.tip s.tipHeight height).map fun (a, ap, _) => (a, ap.signature)
    let now ← wallNanos
    match produceBlockOn s.st e.signer s.tip height approvals newChunks now with
    | .error m =>
      e.log s!"block {height} not produced: {m}"
    | .ok blk =>
      -- a block is never produced twice for a height, not after a restart either
      e.commit #[.set .blockMisc lastProducedBlockKey (u64Bytes height)]
      e.state.modify fun s => { s with latestKnown := max s.latestKnown height }
      e.outbox.modify (·.push (.block blk))
      e.bump "blocksProduced"
      e.log s!"produced block {height} ({newChunks.size} new chunks, {approvals.size} approvals)"
      e.ingestBlock blk

/-- `handle_block_production`: the heights from the first unknown one to the largest with enough
approvals, for which this node is the producer. -/
def Env.tryProduceBlocks (e : Env) : IO Unit := do
  let s ← e.get
  match lift (s.st.epochIdFromPrevBlock s.tip) with
  | .error _ =>
    return
  | .ok epoch =>
    let hi := s.ds.largestThresholdHeight
    let mut h := s.latestKnown + 1
    while h ≤ hi do
      let s ← e.get
      match s.st.blockProducer epoch h with
      | .ok p =>
        if p.accountId == e.me then
          let numShards := ((s.st.epoch epoch).toOption.map (·.layout.shardIds.size)).getD 1
          let now ← e.nowMs
          let (incl, readiness) :=
            match s.inclusion.prepare s.tracker s.st s.tip with
            | .ok i => i.readiness now epoch s.tip numShards
            | .error _ => (s.inclusion, .notReady)
          let (ds, ready) := s.ds.readyToProduce h readiness now
          e.state.modify fun s =>
              { s with
                ds, inclusion := incl }
          if ready then
            e.produceBlock h
      | .error _ =>
        pure ()
      h := h + 1

/-! ### Serving the peer -/

/-- `process_partial_encoded_chunk_request`: the parts asked for that the node has. -/
def Env.serveChunk (e : Env) (author : PeerId) (m : PartialEncodedChunkRequestMsg) : IO Unit := do
  let s ← e.get
  let some c := s.chunks[m.chunkHash.bytes]? | return
  let parts := m.partOrds.filterMap fun o => c.parts[o]?
  let shards := m.trackingShards.entries.map (·.1)
  let receipts := c.receipts.filter fun r => shards.contains r.proof.toShardId
  if parts.isEmpty && receipts.isEmpty then
    return
  let secs ← wallSeconds
  e.outbox.modify
      (·.push
        (routedTo e.nodeKey author (.partialEncodedChunkResponse ⟨m.chunkHash, parts, receipts⟩)
          secs))
  e.bump "chunkRequestsServed"

/-- Parts the peer sent in answer to a request. -/
def Env.onChunkResponse (e : Env) (r : PartialEncodedChunkResponseMsg) : IO Bool := do
  let hash : ChunkHash := ⟨r.chunkHash⟩
  e.bump "PartialEncodedChunkResponse"
  e.state.modify fun s => s.withChunk hash fun x => (x.addParts e.code.total r.parts r.receipts).1
  e.refreshChunk hash

/-! ### Transactions -/

/-- Whether `me` is one of the chunk producers of `shard` in `epoch` (`get_epoch_chunk_producers_for_shard`). -/
def Env.producesShard (e : Env) (s : VState) (epoch : EpochId) (shard : ShardId) : Bool :=
  match s.st.epoch epoch with
  | .ok d =>
    match d.layout.getShardIndex shard with
    | some i =>
      ((d.info.chunkProducersSettlement[i]?).getD #[]).any fun id =>
        (d.info.getValidator id).any (·.accountId == e.me)
    | none => false
  | .error _ => false

/-- `RpcHandlerActor::forward_tx`: the chunk producers of the shard at the next heights (`tx_routing_height_horizon` 4:
the heights 1 to 3 and 7 after the head) get the transaction, and the next epoch's too near the boundary.
The peer is the only node this one talks to. -/
def Env.forwardTx (e : Env) (t : SignedTransaction) : IO Unit := do
  let s ← e.get
  match lift (s.st.epochIdFromPrevBlock s.tip) with
  | .error _ =>
    return
  | .ok epoch =>
    let some layout := (s.st.epoch epoch).toOption.map (·.layout) | return
    let some shard := layout.accountIdToShardId t.transaction.signerId | return
    let mut targets : Array AccountId := #[]
    for horizon in [2, 3, 4, 8] do
      match s.st.chunkProducer epoch (s.tipHeight + (horizon - 1).toUInt64) shard with
      | .ok v =>
        if !targets.contains v.accountId then
          targets := targets.push v.accountId
      | .error _ =>
        pure ()
    for a in targets do
      if a != e.me then
        e.toPeer (.forwardTx t)
        e.bump "txsForwarded"

/-- `RpcHandlerActor::process_tx_internal` on the applied tip. -/
def Env.processTx (e : Env) (t : SignedTransaction) (forwarded : Bool) : IO TxVerdict := do
  let s ← e.get
  match lift (s.st.epochIdFromPrevBlock s.tip) with
  | .error m =>
    return .invalid (.state m)
  | .ok epoch =>
    let some layout := (s.st.epoch epoch).toOption.map (·.layout) | return .noResponse
    let some shard :=
      layout.accountIdToShardId t.transaction.signerId | return .invalid (.state "shard")
    match e.txContext s s.tip shard with
    | .error _ =>
      -- the node has not caught up with its own tip
      if forwarded then
        return .noResponse
      e.forwardTx t
      return .routed
    | .ok ctx =>
      match ctx.checkForPool t with
      | .error why =>
        return .invalid why
      | .ok () =>
        let nextEpoch? := (lift (s.st.nextEpochIdFromPrevBlock s.tip)).toOption
        let producer :=
          e.producesShard s epoch shard || (nextEpoch?.any fun n => e.producesShard s n shard)
        let mut duplicate := false
        if producer then
          let pool := s.pools.getD shard ({} : Pool)
          let (pool', r) := pool.insert t
          e.state.modify fun s => { s with pools := s.pools.insert shard pool' }
          match r with
          | .success =>
            e.bump "txsPooled"
          | .duplicate =>
            duplicate := true
          | .noSpaceLeft =>
            e.bump "txsPoolFull"
        if duplicate then
          return .valid
        let mut active := false
        for i in [1, 2, 3, 4] do
          match s.st.chunkProducer epoch (s.tipHeight + i.toUInt64) shard with
          | .ok v =>
            if v.accountId == e.me then
              active := true
          | .error _ =>
            pure ()
        if active then
          unless forwarded do
            e.forwardTx t
          return .valid
        if !forwarded then
          e.forwardTx t
          return .routed
        return .noResponse

/-- A routed message addressed to this node. -/
def Env.onRouted (e : Env) (m : RoutedMessage) : IO Unit := do
  let changed ←
    match m.body with
    | .blockApproval a =>
      do
        e.collectApproval a true;
        pure false
    | .versionedPartialEncodedChunk c =>
      e.onPartialChunk c
    | .partialEncodedChunkForward f =>
      e.onChunkForward f
    | .partialEncodedChunkResponse r =>
      e.onChunkResponse r
    | .partialEncodedChunkRequest q =>
      do
        e.serveChunk m.author q;
        pure false
    | .versionedChunkEndorsement en =>
      do
        e.onEndorsement en;
        pure false
    | .partialEncodedStateWitness w | .partialEncodedStateWitnessForward w =>
      do
        e.onWitnessPart w;
        pure false
    | .versionedPartialEncodedStateWitness (.v1 w) |
      .versionedPartialEncodedStateWitnessForward (.v1 w) =>
      do
        e.onWitnessPart w;
        pure false
    | .chunkStateWitnessAck _ =>
      do
        e.bump "ChunkStateWitnessAck";
        pure false
    | .forwardTx t =>
      do
        e.bump "ForwardTx"
        match ← e.processTx t true with
        | .invalid why =>
          e.bump "ForwardTxInvalid"
          e.log s!"forwarded transaction {base58Encode t.hash.bytes} refused: {why.describe}"
        | _ =>
          pure ()
        pure false
    | _ =>
      do
        e.bump "OtherRouted";
        pure false
  if changed then
    e.tryApply

/-- The transactions the RPC handed over (`ProcessTxRequest`): each is processed and its sender answered. -/
def Env.drainTxQueue (e : Env) : IO Unit := do
  let queue ← e.txQueue.modifyGet fun q => (q, #[])
  for (t, promise) in queue do
    let verdict ← e.processTx t false
    promise.resolve verdict

/-- The time since the previous turn of the loop. The loop waits at most 20 ms for a message, so a longer gap is
time spent in a turn: the longest one is `loopMaxGapMs` of the report, and a gap of a second or more is logged
and counted (`loopStalls`). -/
def Env.noteTurn (e : Env) : IO Unit := do
  let now ← e.nowMs
  let last ← e.lastTurn.get
  e.lastTurn.set now
  if last != 0 then
    let gap := now - last
    e.state.modify fun s =>
        { s with stats := s.stats.insert "loopMaxGapMs" (max gap (s.stats.getD "loopMaxGapMs" 0)) }
    if gap ≥ 1000 then
      e.bump "loopStalls"
      e.log s!"the event loop was away for {gap} ms"

/-- Whether a block that will move the tip is being applied. Until it is, the tip is stale: the approvals the
timers would send are for a block the node knows it is about to supersede, and a block produced now would have the
stale tip as its parent and compete with the block being applied (with both validators needed for every
threshold, that fork orphans a block of the chain's own tip). Nothing is sent or produced from the tip meanwhile;
the loop goes on with everything else, and the timers restart when the block is applied (`setTip`). -/
def Env.tipIsStale (e : Env) : IO Bool := do
  let s ← e.get
  match ← e.applying.get with
  | some a =>
    match a.block.header.view? with
    | some v =>
      pure (decide (v.height > s.tipHeight))
    | none =>
      pure false
  | none =>
    pure false

/-- One step: the blocks that can be applied, the timer, the production of blocks. -/
def Env.tick (e : Env) : IO Unit := do
  if (← e.failure.get).isSome then
    return
  e.noteTurn
  e.drainTxQueue
  e.tryApply
  let stale ← e.tipIsStale
  if stale then
    e.bump "turnsOnStaleTip"
  else
    let now ← e.nowMs
    let s ← e.get
    let (ds, approvals) := s.ds.processTimer now (some e.signer)
    -- the largest target height is stored before any approval for it is sent (`save_largest_target_height`)
    if ds.largestTargetHeight != s.ds.largestTargetHeight then
      e.commit #[.set .blockMisc largestTargetKey (u64Bytes ds.largestTargetHeight)]
    e.state.modify fun s => { s with ds }
    for a in approvals do
      e.sendApproval a
  e.retryParked
  unless stale do
    e.tryProduceBlocks

end Near.Node.Validator
