import NearNode.Network.Message
import NearNode.Network.Keys
import NearNode.Network.Chunks
import NearNode.Chain.Apply
import NearNode.Chain.Persist
import NearNode.Chain.StateSync
import NearNode.Epoch

/-!
# Syncing the chain from a peer

The syncing observer (nearcore's `chain/client/src/sync`, reduced to one peer and a chain without
forks), in the order nearcore runs it:

1. **Headers** (`HeaderSync`): `BlockHeadersRequest` with a locator, up to 512 headers back, each
   checked as `Chain::sync_block_headers` checks it (`Chain.acceptHeader`) and recorded in the
   chain state, which finalizes an epoch when a header ends it. The header chain keeps growing
   during everything that follows.
2. **State** (`StateSync`, when the chain is far from the genesis): the block `S` whose state is
   synced is found from the headers (`Chain.syncHash`); for every tracked shard the node asks the
   peer for a `ShardStateSyncResponseHeader` and the state parts (routed `StateHeaderRequest` and
   `StatePartRequest`, answered by `VersionedStateResponse` on a Tier 3 connection the peer opens to
   the address in the request), checks the header (`Chain.validateStateHeader`) and every part
   (`Trie.validatePart`), and builds the shard's trie from the parts.
3. **Blocks** (`BlockSync`): the blocks along the header chain from the first block whose chunk
   must be applied (the genesis, or the lowest block of the state sync window), each with the body
   checked (`Chain.attachBody`); the bodies of their new chunks, asked of the peer as routed
   `PartialEncodedChunkRequest`s; a block whose own bodies and its child's are in is handed to the
   apply worker with everything it needs.

The driver runs on the thread that reads the connection and does only work that is small: the
application of blocks is the worker's.
-/

namespace Near.Node.Network

open Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Apply

/-- How the node gets to the head. -/
inductive SyncMode where
  /-- From the genesis, every block (M6). -/
  | blocks
  /-- State sync to the epoch of the head, then blocks. -/
  | state
  /-- State sync when the head is more than a few epochs from the genesis, otherwise blocks. -/
  | auto
  deriving BEq, Inhabited

def SyncMode.parse? : String → Option SyncMode
  | "blocks" => some .blocks
  | "state" => some .state
  | "auto" => some .auto
  | _ => none

/-- A block ready to apply with everything its application reads. -/
structure Work where
  block : Block
  st : Near.Node.Chain.ChainState
  fin : Option Epoch.Finalized
  /-- The transactions of the new chunks, and the receipts that the child block's chunk says this
  chunk sent. -/
  bodies : Std.HashMap UInt64 Body
  /-- The chunk headers of the child block: what the application is compared with. -/
  childChunks : Array ShardChunkHeader
  childHeight : UInt64

/-- The queue between the driver and the apply worker, and what the worker reports back. -/
structure Shared where
  queue : IO.Ref (Array Work)
  /-- The height of the last block applied. -/
  applied : IO.Ref UInt64
  /-- The first thing that went wrong: a block that does not validate, a chunk that does not apply. -/
  failure : IO.Ref (Option String)
  /-- Set to ask every loop to end. -/
  stop : IO.Ref Bool
  /-- The progress of a state sync, which the worker takes in place of its own before the first block. -/
  install : IO.Ref (Option Progress)

def Shared.new (applied : UInt64) : IO Shared := do
  pure
      { queue := ← IO.mkRef #[], applied := ← IO.mkRef applied, failure := ← IO.mkRef none,
        stop := ← IO.mkRef false, install := ← IO.mkRef none }

/-- Records a failure unless one is recorded. -/
def Shared.fail (s : Shared) (msg : String) : IO Unit := do
  s.failure.modify fun f => f.orElse fun _ => some msg

/-- The settings of the driver. -/
structure DriverConfig where
  key : NodeKey
  peer : PeerId
  setup : Epoch.Setup
  /-- Whether bodies are fetched and blocks handed to the worker. -/
  apply : Bool
  mode : SyncMode := .blocks
  /-- The shards whose state is synced and applied; `none` is all of them. -/
  tracked : Option (Array UInt64) := none
  /-- The address the peer connects to with its answers to state requests. -/
  addr : SocketAddr := .v4 (ByteArray.mk #[127, 0, 0, 1]) 0
  /-- Blocks requested at once. -/
  window : Nat := 64
  /-- Chunk bodies requested at once. -/
  chunkWindow : Nat := 64
  /-- Blocks validated beyond the last applied one before the driver waits for the worker. -/
  ahead : Nat := 300
  /-- Milliseconds before a request is sent again. -/
  retryMs : Nat := 4000
  /-- Milliseconds before a state header or part is asked for again. -/
  stateRetryMs : Nat := 5000
  /-- A directory to keep what a state sync receives in (the headers and the block headers around them),
  for the tests of the header checks. -/
  saveDir : Option System.FilePath := none
  /-- Block requests per second (`BlockRequest` is limited to 10 a second by a nearcore peer). -/
  blockRate : Nat := 8
  /-- In `auto` mode the head must be this many epochs from the genesis for a state sync. -/
  autoEpochs : Nat := 3

/-- A validated block waiting for its chunk bodies. -/
structure Staged where
  block : Block
  st : Near.Node.Chain.ChainState
  fin : Option Epoch.Finalized
  /-- The bodies of the new chunks, by shard, as they arrive. -/
  bodies : Std.HashMap UInt64 TransactionReceipt := {}
  /-- The new chunk headers. -/
  needed : Array ShardChunkHeader

/-- A chunk body being fetched. -/
structure ChunkJob where
  parts : ChunkParts
  block : CryptoHash
  /-- When the request went out; the job is not asked again before `retryMs` have passed. -/
  sentAt : Nat

/-- The state of a state sync in progress. -/
structure SyncState where
  /-- The sync block `S` and its parent `P`. -/
  hash : CryptoHash
  prev : CryptoHash
  shards : Array UInt64
  startedAt : Nat
  /-- The blocks between `P` and the lowest chunk the shards' states start at, known once `P` is. -/
  extras : Option (Array CryptoHash) := none
  headers : Std.HashMap UInt64 ShardStart := {}
  headerSent : Std.HashMap UInt64 Nat := {}
  /-- The parts that passed validation, by shard and index: the references they add. -/
  parts : Std.HashMap (UInt64 × UInt64) (Array (CryptoHash × ByteArray × UInt32)) := {}
  partSent : Std.HashMap (UInt64 × UInt64) Nat := {}
  partBytes : Nat := 0
  refused : Nat := 0
  acks : Nat := 0
  busy : Nat := 0
  done : Bool := false
  doneAt : Nat := 0

/-- Everything the driver knows. -/
structure DriverState where
  /-- The chain: every header accepted, and the bodies attached so far. -/
  st : Near.Node.Chain.ChainState
  /-- Headers received and not yet checked. -/
  hdrQueue : Array BlockHeader := #[]
  /-- The child of each accepted block on the chain, to walk forward. -/
  children : Std.HashMap ByteArray CryptoHash := {}
  /-- The epochs the headers finalized, by the hash of the block that ended the epoch before. -/
  finalized : Std.HashMap ByteArray Epoch.Finalized := {}
  lastHeadersRequest : Nat := 0
  /-- Whether the last answer to a header request held headers. -/
  headersFlowing : Bool := true
  /-- The block after which bodies are attached next: the genesis, or the block before the first
  block of a state sync window; none while a state sync waits for the block that tells where. -/
  cursor : Option CryptoHash := none
  /-- Blocks received and not yet attached, by hash. -/
  received : Std.HashMap ByteArray Block := {}
  /-- Block requests in flight: hash to the time of the request. -/
  requested : Std.HashMap ByteArray Nat := {}
  /-- Blocks to ask for whatever the cursor says (the sync block and its parent). -/
  wanted : Array CryptoHash := #[]
  /-- Block requests that may still be sent: a peer drops more than 10 a second (`BlockRequest` in
  `rate_limits/messages_limits.rs`), so the driver sends 8 a second. -/
  tokens : Nat := 8
  lastRefill : Nat := 0
  /-- Validated blocks waiting for bodies, oldest first. -/
  staged : Array Staged := #[]
  jobs : Std.HashMap ByteArray ChunkJob := {}
  /-- The state sync, once started. -/
  sync : Option SyncState := none
  /-- The highest block height the peer reported. -/
  peerHeight : UInt64 := 0
  /-- Counters for the report. -/
  validated : Nat := 0
  headersAccepted : Nat := 0
  handedOver : Nat := 0
  blocksReceived : Nat := 0
  headersReceived : Nat := 0
  chunkPartsRefused : Nat := 0
  chunkResponses : Nat := 0
  /-- The height of the first block validated by this run. -/
  startHeight : UInt64
  /-- The height the headers reached the peer's head at, in milliseconds since the start. -/
  headersDoneAt : Option Nat := none
  /-- The tip of the bodies attached. -/
  bodyTipHeight : UInt64 := 0
  /-- A line for the log, once. -/
  notes : Array String := #[]
  /-- The most recent validated blocks, to serve. -/
  cache : Std.HashMap ByteArray Block := {}

/-- The driver. -/
structure Driver where
  cfg : DriverConfig
  shared : Shared
  state : IO.Ref DriverState
  /-- Messages to send to the peer; the connection loop sends them. -/
  outbox : IO.Ref (Array PeerMessage)
  /-- State sync responses from the Tier 3 connections, which other threads deliver. -/
  inbox : IO.Ref (Array StateResponseInfo)
  clock : IO Nat

def Driver.new (cfg : DriverConfig) (shared : Shared) (st : Near.Node.Chain.ChainState)
    (outbox : IO.Ref (Array PeerMessage)) (clock : IO Nat) : IO Driver := do
  let mut children : Std.HashMap ByteArray CryptoHash := {}
  for (_, r) in st.blocks.toList do
    if r.hash != CryptoHash.zero && r.view.prevHash != CryptoHash.zero then
      children := children.insert r.view.prevHash.bytes r.hash
  let state ←
    IO.mkRef
        { st, children, cursor := if cfg.mode == .blocks then some st.head else none,
          startHeight := st.headHeight, bodyTipHeight := st.headHeight : DriverState }
  pure { cfg, shared, state, outbox, inbox := ← IO.mkRef #[], clock }

private def toHexString (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList (Nat.toDigits 16 (x.toNat + 256)).tail) ""

private def Driver.send (d : Driver) (m : PeerMessage) : IO Unit :=
  d.outbox.modify (·.push m)

/-- The hashes a peer is asked to find a common block in: the newest we know first, then the tip
and its ancestors one, two, four, ... blocks back, down to the genesis. -/
def locator (st : Near.Node.Chain.ChainState) (newest : CryptoHash) (tip : CryptoHash) :
    Array CryptoHash :=
  Id.run do
    let mut out := #[newest]
    if tip != newest then
      out := out.push tip
    let mut cur := tip
    let mut step := 2
    for _ in [0:40] do
      let mut moved := 0
      for _ in [0:step] do
        match st.block cur with
        | .ok r =>
          if r.hash == st.genesisHash then
            break
          cur := r.view.prevHash
          moved := moved + 1
        | .error _ =>
          break
      if moved == 0 then
        break
      out := out.push cur
      step := step * 2
    if out.back? != some st.genesisHash then
      out := out.push st.genesisHash
    return out

/-- A routed message to the peer: signed with the node key, addressed to the peer id. -/
private def Driver.routed (d : Driver) (body : RoutedBody) (now : Nat) : RoutedMessage :=
  let target := PeerIdOrHash.peerId d.cfg.peer
  let author := d.cfg.key.peerId
  let hash := CryptoHash.hashBorsh (target, author, body)
  { target, author, ttl := 100, body, signature := some (d.cfg.key.sign hash.bytes),
    createdAt := some now, numHops := 0 }

/-- `Block::chunks` that the block includes for the first time. -/
private def newChunks (b : Block) : Array ShardChunkHeader :=
  b.chunks.filter fun c => c.isNewChunk b.header.view?.get!.height

/-- Whether this node applies the chunks of `shard`. -/
private def Driver.tracks (d : Driver) (shard : UInt64) : Bool :=
  match d.cfg.tracked with
  | some t => t.contains shard
  | none => true

/-! ### Headers -/

/-- Checks the queued headers in order for a while: each one that is not known and whose parent is
accepted becomes part of the chain; a header that does not validate is a failure. -/
private def Driver.processHeaders (d : Driver) (s : DriverState) (budgetMs : Nat) :
    IO DriverState := do
  let started ← IO.monoMsNow
  let mut s := s
  let mut used := 0
  for h in s.hdrQueue do
    if (← IO.monoMsNow) - started > budgetMs then
      break
    used := used + 1
    if s.st.blockExists h.hash then
      continue
    match Epoch.processHeader d.cfg.setup s.st h with
    | .error e =>
      -- an orphan (its parent is not accepted yet) is dropped; the next request fetches it again
      if e.kind == "DBNotFoundErr" then
        continue
      d.shared.fail s!"header {h.view?.map (·.height) |>.getD 0} rejected: {e.kind} {e.detail}"
      return { s with hdrQueue := #[] }
    | .ok (st', fin) =>
      let some v := h.view? | continue
      s :=
        { s with
          st := st', children := s.children.insert v.prevHash.bytes h.hash,
          headersAccepted := s.headersAccepted + 1
          finalized :=
            match fin with
            | some f => s.finalized.insert h.hash.bytes f
            | none => s.finalized }
  pure { s with hdrQueue := s.hdrQueue.extract used s.hdrQueue.size }

/-- Asks the peer for the headers after what we know. -/
private def Driver.requestHeaders (d : Driver) (s : DriverState) (now : Nat) : IO DriverState := do
  d.send (.blockHeadersRequest (locator s.st s.st.head s.st.head))
  pure { s with lastHeadersRequest := now }

/-! ### State sync -/

/-- Starts the state sync at the block found from the headers, for the tracked shards. -/
private def Driver.startStateSync (d : Driver) (s : DriverState) (hash : CryptoHash) (now : Nat) :
    Except String DriverState := do
  let sync ← (s.st.block hash).mapError (·.kind)
  let layout := (← (s.st.epoch sync.info.epochId).mapError (·.kind)).layout
  let shards := layout.shardIds.filter d.tracks
  if shards.isEmpty then
    throw "no tracked shard is in the shard layout"
  pure
      { s with
        sync := some { hash, prev := sync.view.prevHash, shards, startedAt := now },
        wanted := #[sync.view.prevHash, hash],
        notes :=
          s.notes.push
            s!"state sync at block {sync.view.height} ({hashHex hash}), shards {shards}" }
where hashHex (h : CryptoHash) : String := Trie.hashHex h

/-- The step of the state sync: ask for what is missing, take what arrived. -/
private def Driver.stateStep (d : Driver) (s : DriverState) (now : Nat) : IO DriverState := do
  let some sync := s.sync | return s
  if sync.done then
    return s
  let ms ← IO.monoMsNow
  let mut s := s
  let mut sync := sync
  -- the blocks of the window: the parent's body says which others there are
  if sync.extras.isNone then
    if let some p := s.received[sync.prev.bytes]? then
      let min? :=
        p.chunks.foldl
          (fun m c =>
            some
              (match m with
              | some x => Nat.min x c.heightIncluded.toNat
              | none => c.heightIncluded.toNat))
          none
      match min? with
      | none =>
        d.shared.fail "state sync: the parent of the sync block has no chunks"
      | some minIncluded =>
        let mut extras : Array CryptoHash := #[]
        let mut cur := p.header.view?.get!.prevHash
        for _ in [0:100000] do
          match s.st.block cur with
          | .ok r =>
            if r.view.height.toNat < minIncluded then
              break
            extras := extras.push cur
            cur := r.view.prevHash
          | .error _ =>
            break
        sync := { sync with extras := some extras }
        -- the bodies are attached from the lowest of these blocks
        let lowest := extras.back?.getD sync.prev
        let low ←
          match s.st.block lowest with
          | .ok r =>
            pure r
          | .error e =>
            d.shared.fail e.kind;
            return s
        s :=
          { s with
            cursor := some low.view.prevHash, wanted := s.wanted ++ extras,
            bodyTipHeight := (low.view.height - 1) }
        d.shared.applied.set (low.view.height - 1)
        s :=
          { s with
            notes :=
              s.notes.push
                s!"state sync window: {extras.size + 2} blocks from height {low.view.height}" }
  -- headers and parts
  let total := d.cfg.setup.config.numBlockProducerSeats |> numTotalParts
  discard <| pure total
  for shard in sync.shards do
    match sync.headers[shard]? with
    | none =>
      if
          ms - sync.headerSent.getD shard 0 ≥ d.cfg.stateRetryMs ||
            !sync.headerSent.contains shard then
        d.send (.routed (d.routed (.stateHeaderRequest ⟨shard, sync.hash, d.cfg.addr⟩) now))
        sync := { sync with headerSent := sync.headerSent.insert shard ms }
    | some start =>
      for part in [0:start.numParts.toNat] do
        let key := (shard, part.toUInt64)
        unless sync.parts.contains key do
          if !sync.partSent.contains key || ms - sync.partSent.getD key 0 ≥ d.cfg.stateRetryMs then
            d.send
                (.routed
                  (d.routed (.statePartRequest ⟨shard, sync.hash, part.toUInt64, d.cfg.addr⟩) now))
            sync := { sync with partSent := sync.partSent.insert key ms }
  -- done when every tracked shard has its header and all its parts
  let complete :=
    sync.shards.all fun shard =>
      match sync.headers[shard]? with
      | some start =>
        (List.range start.numParts.toNat).all fun p => sync.parts.contains (shard, p.toUInt64)
      | none => false
  if complete && sync.extras.isSome then
    -- the tries of the shards, from the references the parts add
    let blockRec ←
      match s.st.block sync.hash with
      | .ok r =>
        pure r
      | .error e =>
        d.shared.fail e.kind;
        return { s with sync := some sync }
    let layout ←
      match s.st.epoch blockRec.info.epochId with
      | .ok e =>
        pure e.layout
      | .error e =>
        d.shared.fail e.kind;
        return { s with sync := some sync }
    let mut tables : Store.Tables := {}
    let mut starts : Std.HashMap UInt64 ShardStart := {}
    for shard in sync.shards do
      let some start := sync.headers[shard]? | continue
      let key := shardKey layout shard
      for p in [0:start.numParts.toNat] do
        for (h, data, rc) in sync.parts[(shard, p.toUInt64)]!.toList do
          tables := Store.Tables.apply tables (.rcAdd .state (Store.stateKey key h) data rc.toNat)
      starts := starts.insert shard start
    d.shared.install.set (some { tables, starts })
    if let some dir := d.cfg.saveDir then
      -- the block headers a header check reads, and what is needed to rebuild the chain around them
      let h := blockRec.view.height
      let mut lines : Array String := #[]
      for (_, r) in s.st.blocks.toList do
        if r.hash != CryptoHash.zero && r.view.height + 120 ≥ h && r.view.height ≤ h then
          lines := lines.push (toHexString (Codec.encode r.header))
      IO.FS.writeFile (dir / "headers.txt") ("\n".intercalate lines.toList ++ "\n")
      IO.FS.writeFile (dir / "layout.hex") (toHexString (Codec.encode layout))
      IO.FS.writeFile (dir / "sync.txt")
          s!"{toHexString sync.hash.bytes} {"".intercalate (sync.shards.toList.map (s!"{·} "))}"
    sync :=
      { sync with
        done := true, doneAt := ms }
    s :=
      { s with
        notes :=
          s.notes.push
            s!"state synced: {sync.shards.size} shards, {sync.partBytes} bytes of parts, {sync.refused} refused, in {(ms - sync.startedAt) / 1000} s" }
  pure { s with sync := some sync }

/-- A state sync response from the peer. -/
private def Driver.onStateInfo (d : Driver) (s : DriverState) (info : StateResponseInfo) :
    IO DriverState := do
  let some sync := s.sync | return s
  let (shard, hash, response) :=
    match info with
    | .v1 i => (i.shardId, i.syncHash, ShardStateSyncResponse.v1 i.stateResponse)
    | .v2 i => (i.shardId, i.syncHash, i.stateResponse)
  if hash != sync.hash || !sync.shards.contains shard then
    return s
  let mut sync := sync
  if let some header := response.takeHeader? then
    if sync.headers.contains shard then
      return s
    match validateStateHeader s.st sync.hash shard header with
    | .ok start =>
      sync := { sync with headers := sync.headers.insert shard start }
      if let some dir := d.cfg.saveDir then
        IO.FS.createDirAll dir
        IO.FS.writeBinFile (dir / s!"header-{shard}.bin") (Codec.encode header)
    | .error e =>
      sync := { sync with refused := sync.refused + 1 }
      d.shared.fail s!"shard {shard}: {e}"
  else if let some (idx, part) := response.takePart? then
    let some start := sync.headers[shard]? | return s
    if sync.parts.contains (shard, idx) then
      return s
    if idx ≥ start.numParts then
      sync := { sync with refused := sync.refused + 1 }
    else
      match part.toPartialState? with
      | none =>
        sync := { sync with refused := sync.refused + 1 }
        d.shared.fail s!"shard {shard} part {idx}: the part does not decode"
      | some (.trieValues nodes) =>
        match Trie.validatePart start.root idx start.numParts nodes with
        | .error e =>
          sync := { sync with refused := sync.refused + 1 }
          d.shared.fail s!"shard {shard} part {idx}: {e}"
        | .ok _ =>
          match Trie.applyPart start.root idx start.numParts nodes with
          | .error e =>
            sync := { sync with refused := sync.refused + 1 }
            d.shared.fail s!"shard {shard} part {idx}: {e}"
          | .ok items =>
            sync :=
              { sync with
                parts := sync.parts.insert (shard, idx) items,
                partBytes := sync.partBytes + part.payloadLength }
  else
    -- an empty answer: the peer cannot serve this now
    sync := { sync with busy := sync.busy + 1 }
  pure { s with sync := some sync }

/-! ### Blocks -/

/-- Attaches the bodies of the received blocks that follow the cursor, in order, and stages them. -/
private partial def Driver.attach (d : Driver) (s : DriverState) : IO DriverState := do
  let some cur := s.cursor | return s
  let some next := s.children[cur.bytes]? | return s
  let some block := s.received[next.bytes]? | return s
  let hash := block.header.hash
  match attachBody s.st block with
  | .error e =>
    let height := block.header.view?.map (·.height) |>.getD 0
    d.shared.fail s!"block {height} rejected: {e.kind} {e.detail}"
    pure { s with received := s.received.erase hash.bytes }
  | .ok st' =>
    let v := block.header.view?.get!
    let staged : Staged :=
      { block, st := st', fin := s.finalized[hash.bytes]?,
        needed := if d.cfg.apply then newChunks block else #[] }
    let s :=
      { s with
        st := st', cursor := some hash, bodyTipHeight := v.height,
        received := s.received.erase hash.bytes, requested := s.requested.erase hash.bytes,
        staged := if d.cfg.apply then s.staged.push staged else s.staged,
        validated := s.validated + 1, cache := s.cache.insert hash.bytes block }
    d.attach s

/-- The first staged block that still needs bodies requests them. -/
private def Driver.requestChunks (d : Driver) (s : DriverState) (now : Nat) : IO DriverState := do
  let mut s := s
  let total := d.cfg.setup.config.numBlockProducerSeats |> numTotalParts
  for item in s.staged do
    for h in item.needed do
      if item.bodies.contains h.shardId then
        continue
      let key := h.chunkHash.hash.bytes
      match s.jobs[key]? with
      | some j =>
        if now - j.sentAt ≥ d.cfg.retryMs then
          d.send (.routed (d.routed (.partialEncodedChunkRequest (chunkRequest h total)) now))
          s := { s with jobs := s.jobs.insert key { j with sentAt := now } }
      | none =>
        if s.jobs.size < d.cfg.chunkWindow then
          d.send (.routed (d.routed (.partialEncodedChunkRequest (chunkRequest h total)) now))
          s :=
            { s with
              jobs :=
                s.jobs.insert key
                  { parts := { header := h }, block := item.block.hash, sentAt := now } }
  pure s

/-- Moves the oldest staged blocks to the worker when their bodies and the next block's are in. -/
private partial def Driver.release (d : Driver) (s : DriverState) : IO DriverState := do
  let some first := s.staged[0]? | return s
  let some child := s.staged[1]? | return s
  let complete (x : Staged) : Bool := x.needed.all fun h => x.bodies.contains h.shardId
  if !(complete first && complete child) then
    return s
  let mut bodies : Std.HashMap UInt64 Body := {}
  for h in first.needed do
    let tr := first.bodies[h.shardId]!
    let claimed :=
      match child.bodies[h.shardId]? with
      | some c => c.receipts.map Codec.encode
      | none => #[]
    bodies :=
      bodies.insert h.shardId
        { transactions := tr.transactions, claimedOutgoing := claimed, claimedIncoming := #[],
          prevOutgoing := some (tr.receipts.map Codec.encode) }
  let work : Work :=
    { block := first.block, st := first.st, fin := first.fin, bodies,
      childChunks := child.block.chunks, childHeight := child.block.header.view?.get!.height }
  d.shared.queue.modify (·.push work)
  let s :=
    { s with
      staged := s.staged.extract 1 s.staged.size, handedOver := s.handedOver + 1 }
  d.release s

/-- One step of the driver: check the headers that came, decide where the state comes from, attach
the bodies that came, release what is ready, ask for what is missing. -/
def Driver.tick (d : Driver) : IO Unit := do
  let now ← d.clock
  let ms ← IO.monoMsNow
  let mut s ← d.state.get
  -- the answers of state requests
  for info in ← d.inbox.modifyGet fun i => (i, #[]) do
    s ← d.onStateInfo s info
  s ← d.processHeaders s 150
  -- where the state comes from, once the headers reach the head
  let caughtUp := s.peerHeight > 0 && s.st.headHeight + 2 ≥ s.peerHeight && s.hdrQueue.isEmpty
  if caughtUp && s.headersDoneAt.isNone then
    s := { s with headersDoneAt := some ms }
  if s.cursor.isNone && s.sync.isNone && s.hdrQueue.isEmpty then
    let far :=
      s.st.headHeight.toNat ≥
        s.st.config.genesisHeight.toNat + d.cfg.autoEpochs * s.st.config.epochLength.toNat
    let wantState := d.cfg.mode == .state || (d.cfg.mode == .auto && far)
    if d.cfg.mode == .auto && !far && caughtUp then
      s := { s with cursor := some s.st.genesisHash }
    else if wantState && caughtUp then
      match syncHash s.st s.st.head with
      | .ok (some h) =>
        match d.startStateSync s h ms with
        | .ok s' =>
          s := s'
        | .error e =>
          d.shared.fail s!"state sync: {e}"
      | .ok none =>
        pure ()
      | .error e =>
        d.shared.fail s!"state sync: {e.kind} {e.detail}"
  if s.sync.isSome then
    s ← d.stateStep s now
  s ← d.attach s
  let syncDone := s.sync.all (·.done) || s.sync.isNone
  if d.cfg.apply then
    if syncDone then
      s ← d.release s
    s ← d.requestChunks s ms
  -- blocks along the chain from the cursor, and the ones asked for by hash
  let applied ← d.shared.applied.get
  let waiting := if d.cfg.apply then (s.bodyTipHeight - applied).toNat else 0
  let refill := (ms - s.lastRefill) * d.cfg.blockRate / 1000
  if refill > 0 then
    s :=
      { s with
        tokens := Nat.min d.cfg.blockRate (s.tokens + refill), lastRefill := ms }
  if waiting < d.cfg.ahead then
    let mut ask : Array CryptoHash := s.wanted.filter fun h => !s.st.hasBodyOf h
    if let some cur := s.cursor then
      let mut h := cur
      for _ in [0:d.cfg.window] do
        match s.children[h.bytes]? with
        | some c =>
          ask := ask.push c
          h := c
        | none =>
          break
    for h in ask do
      if s.received.contains h.bytes || s.tokens == 0 then
        continue
      let due :=
        match s.requested[h.bytes]? with
        | some t => decide (ms - t ≥ d.cfg.retryMs)
        | none => true
      if due then
        d.send (.blockRequest h)
        s :=
          { s with
            requested := s.requested.insert h.bytes ms, tokens := s.tokens - 1 }
  -- headers: asked for again as soon as the last answer was processed
  if s.hdrQueue.isEmpty then
    let wait := if s.headersFlowing then 150 else 1000
    if ms - s.lastHeadersRequest ≥ wait then
      s ← d.requestHeaders s ms
  discard <| pure now
  -- the cache of served blocks keeps the latest few thousand
  if s.cache.size > 8192 then
    let keep := s.cache.filter fun _ b => b.header.view?.get!.height + 4096 > s.bodyTipHeight
    s := { s with cache := keep }
  d.state.set s

/-- Headers from the peer. -/
def Driver.onHeaders (d : Driver) (hs : Array BlockHeader) : IO Unit := do
  let mut s ← d.state.get
  s :=
    { s with
      headersReceived := s.headersReceived + hs.size, headersFlowing := !hs.isEmpty }
  for h in hs do
    let some v := h.view? | continue
    if v.height > s.peerHeight then
      s := { s with peerHeight := v.height }
    if !s.st.blockExists h.hash then
      s := { s with hdrQueue := s.hdrQueue.push h }
  d.state.set s

/-- `retrieve_headers`: the headers after the first of `hashes` that we know, at most 512. -/
def Driver.headersAfter (d : Driver) (hashes : Array CryptoHash) : IO (Array BlockHeader) := do
  let s ← d.state.get
  let some start := hashes.find? fun h => s.st.blockExists h | return #[]
  let mut out := #[]
  let mut cur := start
  for _ in [0:512] do
    match s.children[cur.bytes]? with
    | some c =>
      match s.st.block c with
      | .ok r =>
        out := out.push r.header
        cur := c
      | .error _ =>
        break
    | none =>
      break
  return out

/-- A validated block, if it is among the recent ones. -/
def Driver.blockOf (d : Driver) (h : CryptoHash) : IO (Option Block) := do
  pure ((← d.state.get).cache[h.bytes]?)

/-- A block from the peer, asked for or pushed. Its header is checked in its turn. -/
def Driver.onBlock (d : Driver) (b : Block) : IO Unit := do
  let mut s ← d.state.get
  let some v := b.header.view? | return
  s := { s with blocksReceived := s.blocksReceived + 1 }
  if v.height > s.peerHeight then
    s := { s with peerHeight := v.height }
  if !s.received.contains b.header.hash.bytes && !s.st.hasBodyOf b.header.hash then
    s := { s with received := s.received.insert b.header.hash.bytes b }
    if !s.st.blockExists b.header.hash then
      s := { s with hdrQueue := s.hdrQueue.push b.header }
  d.state.set s

/-- A state sync response, delivered by a thread that has no business with the driver's state. -/
def Driver.onStateResponse (d : Driver) (i : StateResponseInfo) : IO Unit :=
  d.inbox.modify (·.push i)

/-- A routed message addressed to this node. -/
def Driver.onRouted (d : Driver) (m : RoutedMessage) : IO Unit := do
  match m.body with
  | .partialEncodedChunkResponse r =>
    let mut s ← d.state.get
    s := { s with chunkResponses := s.chunkResponses + 1 }
    let total := d.cfg.setup.config.numBlockProducerSeats |> numTotalParts
    let data := numDataParts total
    let key := r.chunkHash.bytes
    if let some j := s.jobs[key]? then
      let (parts, refused) := j.parts.add total r
      s := { s with chunkPartsRefused := s.chunkPartsRefused + refused }
      if parts.complete data then
        match parts.body data with
        | .ok body =>
          -- the transactions must be the ones the header's root commits to
          let (root, _) := merklize body.transactions
          if root != j.parts.header.txRoot then
            d.shared.fail
                s!"chunk {toString j.block.bytes.size}: the transactions do not match the tx_root"
          else
            s :=
              { s with
                jobs := s.jobs.erase key,
                staged :=
                  s.staged.map fun x =>
                    if x.block.header.hash == j.block then
                      { x with bodies := x.bodies.insert j.parts.header.shardId body }
                    else x }
        | .error e =>
          d.shared.fail s!"chunk body: {e}"
      else
        s := { s with jobs := s.jobs.insert key { j with parts } }
    d.state.set s
  | .stateRequestAck a =>
    let mut s ← d.state.get
    if let some sync := s.sync then
      let busy := a.body != .willRespond
      s :=
        { s with
          sync :=
            some
              { sync with
                acks := sync.acks + 1, busy := sync.busy + (if busy then 1 else 0) } }
    d.state.set s
  | _ =>
    pure ()

end Near.Node.Network
