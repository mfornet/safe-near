import NearNode.Validator.Tracking
import NearNode.Chain.StateSync
import NearNode.Chain.Header
import NearNode.Trie.StateParts

/-!
# State sync of the shards of the next epoch

`ShardTracker::get_state_sync_info`, `Client::run_catchup` and `StateSync::run_with_shards`
(`chain/client/src/sync/state`), reusing the state sync of the syncing observer (M7: `Chain.syncHash`, `validateStateHeader`,
`Trie.validatePart`, `ShardStart`) for the shards the node tracks in the next epoch and neither tracks now nor tracked in
the epoch before.

1. With the first block of an epoch `T`, `shardsToStateSync` names the shards to sync. The blocks of `T` are applied in
   the `NotCaughtUp` mode: the shards the node already has, not those.
2. When the chain has a sync block (`Chain.syncHash`: the child of the first block with two new chunks of every shard,
   once final), the node asks the peer for each shard's state header and parts (routed requests; the answers come on a
   Tier 3 connection the peer opens to the node's listening address), checks them, and installs the tries.
3. Catching up (`catchup_blocks_step`): the chunks of those shards are applied for every block from the one that
   included the chunk the state precedes, up to the applied tip. The application of new blocks waits for it (nearcore
   catches up beside the chain; here the node has one apply worker, and the catch-up is a few blocks).
4. The job ends; the blocks that follow are applied in the `IsCaughtUp` mode, shards of the next epoch included.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

private def hashHex (h : CryptoHash) : String :=
  Trie.hashHex h

/-- A body with only what the application of a block asks of every chunk. -/
def emptyBodyOf : Body :=
  { transactions := #[], claimedOutgoing := #[], claimedIncoming := #[] }

/-- Starts the job of the epoch `b` begins, if there are shards to sync (`get_catchup_and_state_sync_infos` for the
first block of an epoch). -/
def Env.ensureSyncJob (e : Env) (b : Block) : IO Unit := do
  let s ← e.get
  let some v := b.header.view? | return
  match s.st.isNextBlockEpochStart v.prevHash, s.st.epochIdFromPrevBlock v.prevHash with
  | .ok true, .ok epoch =>
    if s.syncJob.any (·.epoch == epoch) then
      return
    match e.tracker.shardsToStateSync s.st v.prevHash with
    | .ok shards =>
      unless shards.isEmpty do
        let now ← e.nowMs
        e.state.modify fun s =>
            { s with
              syncJob := some { epoch, firstBlock := b.header.hash, shards, startedMs := now } }
        e.log
            s!"state sync: at block {v.height} the node will track shards {shards.toList} next epoch and has not their state"
    | .error err =>
      e.log s!"state sync: {err.kind} {err.detail}"
  | _, _ =>
    pure ()

/-- A state sync response of the peer: a header or a part, checked. -/
def Env.onStateInfo (e : Env) (info : StateResponseInfo) : IO Unit := do
  let s ← e.get
  let some job := s.syncJob | return
  let some syncHash := job.syncHash | return
  let (shard, hash, response) :=
    match info with
    | .v1 i => (i.shardId, i.syncHash, ShardStateSyncResponse.v1 i.stateResponse)
    | .v2 i => (i.shardId, i.syncHash, i.stateResponse)
  if hash != syncHash || !job.shards.contains shard then
    return
  let mut job := job
  if let some header := response.takeHeader? then
    if job.headers.contains shard then
      return
    match validateStateHeader s.st syncHash shard header with
    | .ok start =>
      job := { job with headers := job.headers.insert shard start }
      e.log
          s!"state sync: header of shard {shard}, {start.numParts} parts, chunk included at {start.height}"
    | .error err =>
      job := { job with refused := job.refused + 1 }
      e.log s!"state sync: header of shard {shard} refused: {err}"
  else if let some (idx, part) := response.takePart? then
    let some start := job.headers[shard]? | return
    if job.parts.contains (shard, idx) then
      return
    if idx ≥ start.numParts then
      job := { job with refused := job.refused + 1 }
    else
      match part.toPartialState? with
      | none =>
        job := { job with refused := job.refused + 1 }
        e.log s!"state sync: part {idx} of shard {shard} does not decode"
      | some (.trieValues nodes) =>
        match Trie.validatePart start.root idx start.numParts nodes with
        | .error err =>
          job := { job with refused := job.refused + 1 }
          e.log s!"state sync: part {idx} of shard {shard} refused: {err}"
        | .ok _ =>
          match Trie.applyPart start.root idx start.numParts nodes with
          | .error err =>
            job := { job with refused := job.refused + 1 }
            e.log s!"state sync: part {idx} of shard {shard} refused: {err}"
          | .ok items =>
            job :=
              { job with
                parts := job.parts.insert (shard, idx) items,
                partBytes := job.partBytes + part.payloadLength }
  e.state.modify fun s => { s with syncJob := s.syncJob.map fun _ => job }

/-- Installs the synced tries, and starts applying the chunks of the synced shards on the blocks since. -/
def Env.startCatchup (e : Env) (job : SyncJob) (syncHash : CryptoHash) : IO Unit := do
  let s ← e.get
  let sync ←
    match lift (s.st.block syncHash) with
    | .ok r =>
      pure r
    | .error m =>
      e.failure.modify (fun f => f.orElse fun _ => some s!"state sync: {m}");
      return
  let layout :=
    ((s.st.epoch sync.info.epochId).toOption.map (·.layout)).getD (default : ShardLayout)
  let mut ops : Array Store.Op := #[]
  let mut starts : Std.HashMap UInt64 ShardStart := {}
  for shard in job.shards do
    let some start := job.headers[shard]? | continue
    let key := shardKey layout shard
    for p in [0:start.numParts.toNat] do
      for (h, data, rc) in (job.parts.getD (shard, p.toUInt64) #[]).toList do
        ops := ops.push (.rcAdd .state (Store.stateKey key h) data rc.toNat)
    starts := starts.insert shard start
  e.commit ops
  let tables := ops.foldl Store.Tables.apply s.pr.tables
  let pr0 :=
    { s.pr with
      tables, starts, roots := {} }
  -- the blocks from the lowest chunk the states precede up to the applied tip, on the chain of the tip
  let low := starts.fold (fun m _ st => min m st.height) s.tipHeight
  let mut items : Array (Block × Std.HashMap UInt64 Body) := #[]
  for h in [low.toNat:s.tipHeight.toNat + 1] do
    let some hash := s.canon[h.toUInt64]? | continue
    let some b := s.blocks[hash]? | continue
    let some v := b.header.view? | continue
    let targets := e.bodyShards s.st v.prevHash
    let bodies : Std.HashMap UInt64 Body :=
      b.chunks.foldl
        (fun m c =>
          if c.isNewChunk v.height then
            let body := (s.chunks[c.chunkHash.hash.bytes]?).bind (·.body)
            m.insert c.shardId
              { emptyBodyOf with
                transactions := (body.map (·.transactions)).getD #[],
                proofs := s.chunkProofs c targets }
          else m)
        {}
    items := items.push (b, bodies)
  let params := { e.params with tracked := some job.shards }
  let st := s.st
  let work : AM (Progress × Array (Block × Array ShardReport × Array Store.Op)) := do
    let mut pr := pr0
    let mut out := #[]
    for (b, bodies) in items do
      let (pr', reports, blockOps) ←
        applyBlock none params st b (fun shard => bodies.getD shard emptyBodyOf) pr
      pr := pr'
      out := out.push (b, reports, blockOps)
    return (pr, out)
  let task ← IO.asTask work.run Task.Priority.dedicated
  let now ← e.nowMs
  e.catchingUp.set (some { startedMs := now, starts, task })
  e.state.modify fun s =>
      { s with syncJob := s.syncJob.map fun j => { j with syncedAt := some now } }
  e.log
      s!"state sync: state of shards {job.shards.toList} installed ({job.partBytes} bytes of parts), catching up {items.size} blocks from height {low}"

/-- Takes up a finished catch-up: the progress, the store operations, what the RPC serves of the outcomes; the job ends. -/
def Env.finishCatchup (e : Env) (c : CatchingUp) : IO Unit := do
  let result : Except String (Progress × Array (Block × Array ShardReport × Array Store.Op)) :=
    match c.task.get with
    | .ok r => r
    | .error err => .error s!"the thread failed: {err}"
  match result with
  | .error m =>
    e.failure.modify fun f => f.orElse fun _ => some s!"state sync catch-up failed: {m}"
  | .ok (pr, blocks) =>
    let s0 ← e.get
    -- the compiled code the replays decoded meanwhile stays
    let merged : CodeCache :=
      { pr.cache with
        byLabel :=
          s0.pr.cache.byLabel.fold (fun m k x => if m.contains k then m else m.insert k x)
            pr.cache.byLabel }
    e.state.modify fun s => { s with pr := { pr with cache := merged } }
    for (b, reports, chunkOps) in blocks do
      let some v := b.header.view? | continue
      let s1 ← e.get
      let (extraOps, s2) := appliedOps s1 b reports
      e.commit
          (chunkOps.filter
              (fun
                | .set .incomingReceipts _ _ => false
                | _ => true) ++
            extraOps)
      e.state.modify fun s =>
          { s with
            outcomes := s2.outcomes, txIndex := s2.txIndex, receiptsById := s2.receiptsById,
            deliveredAt := s2.deliveredAt }
      e.writeAppliedLog b reports (fun _ => emptyBodyOf)
      discard <| pure v
    -- the block before the first chunk of a synced state: the state root it left, for the witnesses that start there
    for (shard, start) in c.starts.toList do
      let s1 ← e.get
      if let some hash := s1.canon[start.height]? then
        if let .ok r := s1.st.block ⟨hash⟩ then
          let fake : ChunkExtra :=
            .v5
              { stateRoot := start.root, outcomeRoot := CryptoHash.zero, validatorProposals := #[],
                gasUsed := 0, gasLimit := 0, balanceBurnt := ⟨0⟩, congestionInfo := default,
                bandwidthRequests := default, proposedSplit := none }
          unless s1.pr.extras.contains (r.view.prevHash.bytes, shard) do
            e.state.modify fun s =>
                { s with
                  pr :=
                    { s.pr with extras := s.pr.extras.insert (r.view.prevHash.bytes, shard) fake } }
    e.catchingUp.set none
    let took := (← e.nowMs) - c.startedMs
    e.state.modify fun s => ({ s with syncJob := none }).bump "stateSyncs"
    e.log
        s!"state sync: caught up in {took} ms; the node applies the shards of the next epoch from now on"

/-- One step of the state sync: the sync block, the requests, the responses, the installation, the catch-up. -/
def Env.stepSync (e : Env) : IO Unit := do
  let s ← e.get
  let some job := s.syncJob | return
  if job.syncedAt.isSome then
    if let some c← e.catchingUp.get then
      if ← IO.hasFinished c.task then
        e.finishCatchup c
    return
  let now ← e.nowMs
  -- the sync block, from the headers
  if job.syncHash.isNone then
    match s.st.epochIdOf s.st.head with
    | .ok epoch =>
      if epoch != job.epoch then
        e.log
            "state sync: the epoch ended before the sync block was known; the shards will not be ready"
        e.state.modify fun s => { s with syncJob := none }
        return
    | .error _ =>
      pure ()
    match Chain.syncHash s.st s.st.head with
    | .ok (some h) =>
      e.state.modify fun s =>
          { s with syncJob := s.syncJob.map fun j => { j with syncHash := some h } }
      e.log s!"state sync: sync block {hashHex h}"
    | _ =>
      pure ()
    return
  let some syncHash := job.syncHash | return
  -- the answers that came in
  for info in (← e.stateInbox.modifyGet fun x => (x, #[])) do
    e.onStateInfo info
  let job ←
    (do
        let s ← e.get
        pure (s.syncJob.getD job))
  -- the requests
  let mut headerSent := job.headerSent
  let mut partSent := job.partSent
  for shard in job.shards do
    match job.headers[shard]? with
    | none =>
      if now - headerSent.getD shard 0 ≥ 5000 || !headerSent.contains shard then
        e.toPeer (.stateHeaderRequest ⟨shard, syncHash, e.syncAddr⟩)
        headerSent := headerSent.insert shard now
    | some start =>
      for part in [0:start.numParts.toNat] do
        let key := (shard, part.toUInt64)
        unless job.parts.contains key do
          if !partSent.contains key || now - partSent.getD key 0 ≥ 5000 then
            e.toPeer (.statePartRequest ⟨shard, syncHash, part.toUInt64, e.syncAddr⟩)
            partSent := partSent.insert key now
  e.state.modify fun s =>
      { s with
        syncJob :=
          s.syncJob.map fun j =>
            { j with
              headerSent, partSent } }
  let complete :=
    job.shards.all fun shard =>
      match job.headers[shard]? with
      | some start =>
        (List.range start.numParts.toNat).all fun p => job.parts.contains (shard, p.toUInt64)
      | none => false
  if complete && (← e.applying.get).isNone then
    e.startCatchup job syncHash

end Near.Node.Validator
