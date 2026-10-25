import NearNode.Network.Message
import NearNode.Network.Keys
import NearNode.Network.Chunks
import NearNode.Chain.Apply
import NearNode.Chain.Persist
import NearNode.Epoch

/-!
# Syncing the chain from a peer

The block-fetching half of the node (nearcore's `chain/client/src/sync`, reduced to one peer and a
chain without forks): the headers after the tip (`BlockHeadersRequest` with a locator, up to 512
headers back), the blocks they name (`BlockRequest`), every block validated in order by
`Epoch.processBlock` (header, approvals, chunk headers, endorsements: M5a) as soon as its parent is
validated, and, to apply a block, the bodies of its new chunks, asked of the peer as routed
`PartialEncodedChunkRequest`s. A block whose chunks have their bodies, and whose child block has
too, is handed to the apply worker with everything it needs (the child's bodies carry the outgoing
receipts of the block's chunks, which also give the code a contract deploys from its own memory, and
a check on the receipts the Lean runtime produced).

The driver runs on the thread that reads the connection and only does work that is small: the
application of blocks is the worker's.
-/

namespace Near.Node.Network

open Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Apply

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

def Shared.new (applied : UInt64) : IO Shared := do
  pure
      { queue := ← IO.mkRef #[], applied := ← IO.mkRef applied, failure := ← IO.mkRef none,
        stop := ← IO.mkRef false }

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
  /-- Blocks requested at once. -/
  window : Nat := 64
  /-- Chunk bodies requested at once. -/
  chunkWindow : Nat := 64
  /-- Blocks validated beyond the last applied one before the driver waits for the worker. -/
  ahead : Nat := 300
  /-- Milliseconds before a request is sent again. -/
  retryMs : Nat := 4000

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

/-- Everything the driver knows. -/
structure DriverState where
  st : Near.Node.Chain.ChainState
  tipHash : CryptoHash
  tipHeight : UInt64
  /-- Headers after the tip that chain together, in order. -/
  pending : Array CryptoHash := #[]
  /-- Blocks received and not yet validated, by hash. -/
  received : Std.HashMap ByteArray Block := {}
  /-- Block requests in flight: hash to the time of the request. -/
  requested : Std.HashMap ByteArray Nat := {}
  lastHeadersRequest : Nat := 0
  /-- Block requests that may still be sent: a peer drops more than 10 a second (`BlockRequest` in
  `rate_limits/messages_limits.rs`), so the driver sends 8 a second. -/
  tokens : Nat := 8
  lastRefill : Nat := 0
  /-- Validated blocks waiting for bodies, oldest first. -/
  staged : Array Staged := #[]
  jobs : Std.HashMap ByteArray ChunkJob := {}
  /-- The highest block height the peer reported. -/
  peerHeight : UInt64 := 0
  /-- Counters for the report. -/
  validated : Nat := 0
  handedOver : Nat := 0
  blocksReceived : Nat := 0
  headersReceived : Nat := 0
  chunkPartsRefused : Nat := 0
  chunkResponses : Nat := 0
  /-- The height of the first block validated by this run. -/
  startHeight : UInt64
  /-- The child of each validated block, to serve headers after a block. -/
  next : Std.HashMap ByteArray CryptoHash := {}
  /-- The most recent validated blocks, to serve. -/
  cache : Std.HashMap ByteArray Block := {}

/-- The driver. -/
structure Driver where
  cfg : DriverConfig
  shared : Shared
  state : IO.Ref DriverState
  /-- Messages to send to the peer; the connection loop sends them. -/
  outbox : IO.Ref (Array PeerMessage)
  clock : IO Nat

def Driver.new (cfg : DriverConfig) (shared : Shared) (st : Near.Node.Chain.ChainState)
    (outbox : IO.Ref (Array PeerMessage)) (clock : IO Nat) : IO Driver := do
  let state ←
    IO.mkRef
        { st, tipHash := st.head, tipHeight := st.headHeight, startHeight := st.headHeight :
          DriverState }
  pure { cfg, shared, state, outbox, clock }

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

/-- Asks the peer for the headers after what we know. -/
private def Driver.requestHeaders (d : Driver) (s : DriverState) (now : Nat) : IO DriverState := do
  let newest := s.pending.back?.getD s.tipHash
  d.send (.blockHeadersRequest (locator s.st newest s.tipHash))
  pure { s with lastHeadersRequest := now }

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

/-- Validates the received blocks that follow the tip, in order. -/
private partial def Driver.validate (d : Driver) (s : DriverState) (now : Nat) : IO DriverState :=
  do
  -- the next block: the first pending hash, or any received block whose parent is the tip
  let next? :=
    match s.pending[0]? with
    | some h => s.received[h.bytes]?
    | none => none
  match next? with
  | none =>
    pure s
  | some block =>
    let some v := block.header.view? |
      do
        d.shared.fail "block with an unsupported header";
        pure s
    if v.prevHash != s.tipHash then
      -- the headers and the chain disagree: drop what we have and ask again
      pure
          { s with
            pending := #[], requested := {}, received := {}, lastHeadersRequest := 0 }
    else
      match Epoch.processBlock d.cfg.setup s.st block with
      | .error e =>
        d.shared.fail s!"block {v.height} rejected: {e.kind} {e.detail}"
        pure
            { s with
              pending := #[], received := s.received.erase block.header.hash.bytes }
      | .ok (st', fin) =>
        let hash := block.header.hash
        let staged : Staged :=
          { block, st := st', fin, needed := if d.cfg.apply then newChunks block else #[] }
        let s :=
          { s with
            st := st', tipHash := hash, tipHeight := v.height,
            pending := s.pending.extract 1 s.pending.size, received := s.received.erase hash.bytes,
            requested := s.requested.erase hash.bytes,
            staged := if d.cfg.apply then s.staged.push staged else s.staged,
            validated := s.validated + 1, next := s.next.insert s.tipHash.bytes hash,
            cache := s.cache.insert hash.bytes block }
        d.validate s now

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
        { transactions := tr.transactions, claimedOutgoing := claimed, claimedIncoming := #[] }
  let work : Work :=
    { block := first.block, st := first.st, fin := first.fin, bodies,
      childChunks := child.block.chunks, childHeight := child.block.header.view?.get!.height }
  d.shared.queue.modify (·.push work)
  let s :=
    { s with
      staged := s.staged.extract 1 s.staged.size, handedOver := s.handedOver + 1 }
  d.release s

/-- One step of the driver: validate what can be, release what is ready, ask for what is missing. -/
def Driver.tick (d : Driver) : IO Unit := do
  let now ← d.clock
  let ms ← IO.monoMsNow
  let mut s ← d.state.get
  s ← d.validate s ms
  if d.cfg.apply then
    s ← d.release s
    s ← d.requestChunks s ms
  -- blocks for the headers we have
  let applied ← d.shared.applied.get
  let waiting := if d.cfg.apply then (s.tipHeight - applied).toNat else 0
  let refill := (ms - s.lastRefill) * 8 / 1000
  if refill > 0 then
    s :=
      { s with
        tokens := Nat.min 8 (s.tokens + refill), lastRefill := ms }
  if waiting < d.cfg.ahead then
    for h in s.pending.extract 0 d.cfg.window do
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
  -- headers: when none are pending, and now and then to hear of a block we missed
  if
      s.pending.size < 8 &&
        ms - s.lastHeadersRequest ≥ (if s.pending.isEmpty then 1500 else 4000) then
    s ← d.requestHeaders s ms
  discard <| pure now
  -- the cache of served blocks keeps the latest few thousand
  if s.cache.size > 8192 then
    let keep := s.cache.filter fun _ b => b.header.view?.get!.height + 4096 > s.tipHeight
    s := { s with cache := keep }
  d.state.set s

/-- Headers from the peer. -/
def Driver.onHeaders (d : Driver) (hs : Array BlockHeader) : IO Unit := do
  let mut s ← d.state.get
  s := { s with headersReceived := s.headersReceived + hs.size }
  let mut expected := s.pending.back?.getD s.tipHash
  for h in hs do
    let some v := h.view? | continue
    if v.height > s.peerHeight then
      s := { s with peerHeight := v.height }
    if v.prevHash == expected then
      s := { s with pending := s.pending.push h.hash }
      expected := h.hash
  d.state.set s

/-- `retrieve_headers`: the headers after the first of `hashes` that we know, at most 512. -/
def Driver.headersAfter (d : Driver) (hashes : Array CryptoHash) : IO (Array BlockHeader) := do
  let s ← d.state.get
  let some start := hashes.find? fun h => s.st.blockExists h | return #[]
  let mut out := #[]
  let mut cur := start
  for _ in [0:512] do
    match s.next[cur.bytes]? with
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

/-- A block from the peer, asked for or pushed. -/
def Driver.onBlock (d : Driver) (b : Block) : IO Unit := do
  let mut s ← d.state.get
  let some v := b.header.view? | return
  s := { s with blocksReceived := s.blocksReceived + 1 }
  if v.height > s.peerHeight then
    s := { s with peerHeight := v.height }
  if v.height > s.tipHeight && !s.received.contains b.header.hash.bytes then
    s := { s with received := s.received.insert b.header.hash.bytes b }
    -- a pushed block that follows the pending headers needs no request for its header
    if s.pending.isEmpty && v.prevHash == s.tipHash then
      s := { s with pending := #[b.header.hash] }
    else if s.pending.back? == some v.prevHash then
      s := { s with pending := s.pending.push b.header.hash }
  d.state.set s

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
  | _ =>
    pure ()

end Near.Node.Network
