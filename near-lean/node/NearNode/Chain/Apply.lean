import NearNode.Chain.ApplyChunk
import NearNode.Chain.StateChanges
import NearNode.Chain.Profile
import NearNode.Epoch
import NearNode.Trie
import NearNode.Store

/-!
# Applying the chunks of a block

What `Chain::postprocess_block` and `apply_chunks` do for an accepted block: for every shard the
incoming receipts the block's new chunks carry for it (`collect_incoming_receipts_from_chunks`) and
those delivered since its last chunk (`get_incoming_receipts_for_shard`), the context of the chunk
(`ApplyChunkBlockContext`, `NightshadeRuntime::process_state_update`), the runtime, the new state in
the shard's trie, and the `ChunkExtra` that nearcore stores for the block and the shard. A shard
whose chunk is missing in the block gets `apply_old_chunk`: the epoch's accounts update and the
scheduler, and the previous `ChunkExtra` with the new state root.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Trie

/-- The body of a chunk as the block carries it: the transactions and, for the checks, the receipts
that applying the chunk sent according to nearcore and the receipts it was delivered. -/
structure Body where
  transactions : Array SignedTransaction
  claimedOutgoing : Array ByteArray
  claimedIncoming : Array ByteArray
  /-- The `prev_outgoing_receipts` of the chunk's own body: what the chunk before it sent, which is
  where `collect_incoming_receipts_from_chunks` reads the receipts the block delivers. Without it
  (the corpus does not have it) they are the outgoing receipts of the previous chunk as this node
  applied it. -/
  prevOutgoing : Option (Array ByteArray) := none
  /-- The receipts the chunk's predecessor sent to the shards the node tracks, by receiving shard, from the receipt
  proofs of the partial chunk (`PartialEncodedChunk::prev_outgoing_receipts`): all a node that does not apply the
  chunk's shard has of what that chunk's predecessor sent. -/
  proofs : Option (Array (UInt64 × Array ByteArray)) := none

/-- The parameters of the chain. -/
structure Params where
  setup : Epoch.Setup
  cfg : Wasm.Near.RuntimeConfig
  congestion : Near.Congestion.Config
  protocol : Nat
  chainId : String
  /-- Whether each chunk's pre-state is converted back and compared with the trie's entries (a test of
  the conversion; the sync node leaves it off). -/
  roundTrip : Bool := true
  /-- The shards whose chunks are applied; `none` is all of them (`tracked_shards_config`). -/
  tracked : Option (Array UInt64) := none

/-- A shard's place in a state sync: the state before the chunk included at `height` is `root`, and
`delivered` are the receipts to apply with it (the blocks from that height back to the previous chunk,
newest first); `incoming` are the receipts of every block of the header, newest first. -/
structure ShardStart where
  shard : ShardId
  syncHash : CryptoHash
  height : BlockHeight
  root : CryptoHash
  numParts : UInt64
  memoryUsage : UInt64
  /-- The height of the chunk before the one at `height` (zero at the genesis). -/
  prevHeight : BlockHeight
  transactions : Array SignedTransaction
  delivered : Array ByteArray
  incoming : Array (CryptoHash × Array ByteArray)
  rootNode : StateRootNode

/-- What the node knows about the chunks applied so far. -/
structure Progress where
  /-- The nodes of every shard's trie, the chunk extras and the receipts, as the store keeps them. -/
  tables : Store.Tables := {}
  /-- The state root of every shard after the last block. -/
  roots : Std.HashMap UInt64 CryptoHash := {}
  /-- The receipts each chunk applied at a block sent, by block hash and shard. -/
  outgoing : Std.HashMap (ByteArray × UInt64) (Array ByteArray) := {}
  extras : Std.HashMap (ByteArray × UInt64) ChunkExtra := {}
  /-- The receipts each block delivers to each shard in the order they are applied
  (`save_incoming_receipt`), kept for shards whose chunk is missing. -/
  incoming : Std.HashMap (ByteArray × UInt64) (Array ByteArray) := {}
  cache : CodeCache := {}
  /-- Shards synced from a peer's state that have not had their first chunk applied: the state
  before the chunk included at the start's height is in `tables` (state sync, M7). -/
  starts : Std.HashMap UInt64 ShardStart := {}

/-- The result of one chunk. -/
structure ShardReport where
  shard : UInt64
  extra : ChunkExtra
  incoming : Array ByteArray
  outgoing : Array ByteArray
  /-- Whether the conversion of the pre-state encoded back to the trie's entries. -/
  roundTrip : Bool
  outcomes : Array ExecutionOutcomeWithId := #[]
  /-- The yielded receipts the chunk stored, as Borsh receipts. -/
  yielded : Array ByteArray := #[]

/-! ### Chunk header fields -/

def congestionOf : ShardChunkHeader → Option CongestionInfo
  | .v3 h =>
    match h.inner with
    | .v4 i => some i.congestionInfo
    | .v5 i => some i.congestionInfo
    | _ => none
  | _ => none

def requestsOf : ShardChunkHeader → Option BandwidthRequests
  | .v3 h =>
    match h.inner with
    | .v4 i => some i.bandwidthRequests
    | .v5 i => some i.bandwidthRequests
    | _ => none
  | _ => none

private def bytesOf (l : List UInt8) : ByteArray :=
  ⟨l.toArray⟩

private def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList (Nat.toDigits 16 (x.toNat + 256)).tail) ""

/-! ### Trie access -/

/-- `ShardUId` as the `State` column and the per-shard columns key it. -/
def shardKey (layout : ShardLayout) (shard : UInt64) : ByteArray :=
  Store.shardUIdKey layout.version shard.toUInt32

/-- The key of a per-block, per-shard column (`get_block_shard_uid`). -/
def blockShardKey (block : CryptoHash) (layout : ShardLayout) (shard : UInt64) : ByteArray :=
  block.bytes ++ shardKey layout shard

/-- All entries of a shard's trie. -/
def trieEntries (src : NodeSource) (root : CryptoHash) :
    Except String (Array (ByteArray × ByteArray)) := do
  let refs ← Trie.entries src root
  refs.mapM fun (k, r) =>
      match src.read r.hash with
      | some v => pure (k, v)
      | none => throw "trie value missing"

/-- The entries of a shard by key. -/
def entryMap (es : Array (ByteArray × ByteArray)) : Std.HashMap ByteArray ByteArray :=
  es.foldl (fun m (k, v) => m.insert k v) {}

/-- The entries that differ between the entries `old` and `new` of a shard (`oldMap` and `newMap` are the same by key): the new
value, or `none` for an entry that is gone. -/
def diffEntries (old new : Array (ByteArray × ByteArray))
    (oldMap newMap : Std.HashMap ByteArray ByteArray) : Array Change :=
  Id.run do
    let mut changes : Array Change := #[]
    for (k, v) in new do
      if oldMap[k]? != some v then
        changes := changes.push (k, some v)
    for (k, _) in old do
      if !newMap.contains k then
        changes := changes.push (k, none)
    return changes

/-! ### Receipts -/

/-- `Receipt::receiver_shard_id`: the shard of the receiver, or the target shard of a global
contract distribution. -/
def receiverShard (layout : ShardLayout) (r : ByteArray) : Except String UInt64 := do
  match Codec.decodeAll (α := Receipt) r with
  | .error e =>
    throw s!"receipt does not decode: {repr e}"
  | .ok (.v0 r) =>
    match r.receipt with
    | .globalContractDistribution (.v1 d) =>
      pure d.targetShard
    | .globalContractDistribution (.v2 d) =>
      pure d.targetShard
    | _ =>
      match layout.accountIdToShardId r.receiverId with
      | some s =>
        pure s
      | none =>
        throw "receiver has no shard"

/-- `create_receipts_proofs_from_outgoing_receipts`: the outgoing receipts of one chunk grouped by
the shard that receives them, one group per shard of the layout in index order. -/
def groupByShard (layout : ShardLayout) (receipts : Array ByteArray) :
    Except String (Array (Array ByteArray)) := do
  let mut groups : Array (Array ByteArray) := Array.replicate layout.numShards.toNat #[]
  for r in receipts do
    let shard ← receiverShard layout r
    let some index := layout.getShardIndex shard | throw "receiver shard not in the layout"
    groups := groups.modify index (·.push r)
  return groups

/-- `build_receipts_hashes`: one hash of `(shard_id, receipts)` per shard in index order. -/
def receiptHashes (layout : ShardLayout) (groups : Array (Array ByteArray)) :
    Except String (Array CryptoHash) := do
  let mut out : Array CryptoHash := #[]
  for i in [0:groups.size] do
    let some id := layout.getShardId i | throw "shard index out of range"
    let receipts ←
      (groups[i]!).mapM fun r =>
          match Codec.decodeAll (α := Receipt) r with
          | .ok r => pure r
          | .error e => throw s!"receipt does not decode: {repr e}"
    out := out.push (CryptoHash.hashBorsh (id, receipts))
  return out

/-- What the previous chunk of a new chunk sent: all of it, or the part addressed to some shards (the proofs of the
partial chunk). -/
inductive SentReceipts where
  | full (receipts : Array ByteArray)
  | toShards (groups : Array (UInt64 × Array ByteArray))

/-- The receipts of one chunk grouped by receiving shard in index order; the shards a partial chunk has no proof for
are empty. -/
def SentReceipts.byShard (layout : ShardLayout) :
    SentReceipts → Except String (Array (Array ByteArray))
  | .full r => groupByShard layout r
  | .toShards gs => do
    let mut groups : Array (Array ByteArray) := Array.replicate layout.numShards.toNat #[]
    for (shard, rs) in gs do
      let some index :=
        layout.getShardIndex shard | throw "receipt proof for a shard not in the layout"
      groups := groups.set! index rs
    return groups

/-- The receipts every shard is delivered by a block (`collect_incoming_receipts_from_chunks`): each
new chunk contributes the receipts its previous chunk sent, grouped by receiving shard, and the
contributions to a shard are shuffled with the previous block's hash as the seed. `sent` has an entry
for every chunk of the block (index order) and `none` for a chunk that is not new. -/
def incomingReceipts (layout : ShardLayout) (prevHash : CryptoHash)
    (sent : Array (Option SentReceipts)) : Except String (Array (Array ByteArray)) := do
  let grouped ← sent.filterMapM fun s => s.mapM (·.byShard layout)
  let mut result : Array (Array ByteArray) := #[]
  for target in [0:layout.numShards.toNat] do
    let proofs : Array (Array ByteArray) := grouped.map (·[target]!)
    let (shuffled, _) := (ChaCha20Rng.fromSeed prevHash.bytes).shuffle proofs
    result := result.push (shuffled.foldl (· ++ ·) #[])
  return result

/-- The block of the chain at `height`, walking back from `rec`. -/
def blockAtHeight (st : Near.Node.Chain.ChainState) (rec : BlockRec) (height : BlockHeight) :
    Except String BlockRec := do
  let mut cur := rec
  for _ in [0:100000] do
    if cur.view.height == height then
      return cur
    if cur.view.height < height then
      break
    cur ← (st.block cur.view.prevHash |>.mapError (·.kind))
  throw s!"no block at height {height} below {rec.view.height}"

/-! ### The context of a chunk -/

def modelUpdate (u : Epoch.AccountsUpdate) : Near.ValidatorAccountsUpdate :=
  let pairs (xs : Array (AccountId × Balance)) := xs.toList.map fun (a, b) => (a.val, b.val)
  { stakeInfo := pairs u.stakeInfo, validatorRewards := pairs u.validatorRewards,
    lastProposals := pairs u.lastProposals, protocolTreasury := u.protocolTreasury.map (·.val) }

/-- `EpochInfoProvider` for a chunk: the minimum stake for `Stake` actions and the stakes of the
validators of the block's epoch. -/
def providerOf (p : Params) (st : Near.Node.Chain.ChainState) (prev : CryptoHash)
    (epoch : EpochId) : Result Near.EpochInfo := do
  let nextId ← st.nextEpochIdFromPrevBlock prev
  let next := (← st.epoch nextId).info.view
  let validators := (← st.epoch epoch).info.view.validators
  pure
      { minimumStake := next.seatPrice.val / p.setup.config.minimumStakeDivisor,
        totalStake := validators.foldl (fun s v => s + v.stake.val) 0,
        validators := validators.toList.map fun v => (v.accountId.val, v.stake.val) }

/-- The scheduler's view of the network, from the chunk headers of the block. -/
def schedulerInput (block : Block) (layout : ShardLayout) (prevHash : CryptoHash) :
    Except String ChainReplay.ShardChunk.Input := do
  let height := block.header.view?.map (·.height) |>.getD 0
  let mut congestion : List (Nat × Near.ShardSink.ShardCongestion) := []
  let mut requests : Array (ShardId × BandwidthRequests) := #[]
  for c in block.chunks do
    let some info := congestionOf c | throw "chunk header without congestion info"
    let parsed ← Near.Congestion.Info.ofBorsh (Codec.encode info).toList
    congestion :=
      congestion ++
        [(c.shardId.toNat, { info := parsed, missedChunks := (height - c.heightIncluded).toNat })]
    if let some r := requestsOf c then
      requests := requests.push (c.shardId, r)
  let sortedRequests := requests.qsort fun a b => a.1 < b.1
  let modelLayout ← Near.Sharding.ShardLayout.ofBorsh (Codec.encode layout).toList
  pure
      { layout := modelLayout, congestion := congestion.mergeSort fun a b => a.1 ≤ b.1,
        requests := ← Near.Bandwidth.blockRequestsOfBorsh (Codec.encode sortedRequests).toList,
        prevBlockHash := prevHash.bytes.toList }

/-- The context of the chunk of `chunk.shardId` in the block with header view `v`, whose previous block is `prevRec`
(`ApplyChunkBlockContext` and `ApplyState` of `NightshadeRuntime::process_state_update`). -/
def chunkContext (p : Params) (v : HeaderView) (epoch : Near.Node.Chain.EpochData)
    (prevRec : BlockRec) (chunk : ShardChunkHeader) (layout : ShardLayout)
    (provider : Near.EpochInfo) (update : Option Epoch.AccountsUpdate)
    (input : ChainReplay.ShardChunk.Input) : ChunkContext :=
  { protocol := p.protocol, height := v.height.toNat, timestamp := v.timestamp.toNat,
    epochHeight := epoch.info.view.epochHeight, gasPrice := prevRec.view.nextGasPrice.val,
    gasLimit := chunk.gasLimit.toNat, randomSeed := v.randomValue.bytes.toList,
    chainId := p.chainId, shardId := chunk.shardId.toNat,
    shardIds := layout.shardIds.toList.map (·.toNat), epochInfo := provider,
    update := update.map modelUpdate, scheduler := input }

/-! ### Applying a block -/

/-- A chain-state answer as a failure message. -/
private def lifted (r : Near.Node.Chain.Result α) : AM α :=
  ExceptT.mk (pure (r.mapError (·.kind)))

/-- Apply the chunks of an accepted block. `body shard` is the chunk's body. Returns the progress,
a report per shard and the store operations of the block. -/
def applyBlock (prof : Option Prof) (p : Params) (st : Near.Node.Chain.ChainState) (block : Block)
    (body : UInt64 → Body) (pr : Progress) : AM (Progress × Array ShardReport × Array Store.Op) :=
  do
  let hash := block.header.hash
  let some v := block.header.view? | throw "header version"
  let rec_ ← lifted (st.block hash)
  let epochId := rec_.info.epochId
  let epoch ← lifted (st.epoch epochId)
  let layout := epoch.layout
  let prevRec ← lifted (st.block v.prevHash)
  -- what the previous chunk of each new chunk sent: the receipts of the block that included it
  let mut sent : Array (Option SentReceipts) := #[]
  for index in [0:block.chunks.size] do
    let c := block.chunks[index]!
    if c.isNewChunk v.height then
      match (body c.shardId).prevOutgoing with
      | some r =>
        sent := sent.push (some (.full r))
      | none =>
        let some prevChunk := prevRec.chunks[index]? | throw "previous chunk missing"
        let included ← blockAtHeight st prevRec prevChunk.heightIncluded
        match pr.outgoing[(included.hash.bytes, c.shardId)]? with
        | some r =>
          sent := sent.push (some (.full r))
        | none =>
          match (body c.shardId).proofs with
          | some groups =>
            sent := sent.push (some (.toShards groups))
          | none =>
            throw s!"no outgoing receipts of shard {c.shardId} at height {prevChunk.heightIncluded}"
    else
      sent := sent.push none
  let incoming ← incomingReceipts layout v.prevHash sent
  let provider ← lifted (providerOf p st v.prevHash epochId)
  let input ← schedulerInput block layout v.prevHash
  let mut pr := pr
  let mut reports : Array ShardReport := #[]
  let mut ops : Array Store.Op := #[]
  for index in [0:block.chunks.size] do
    let chunk := block.chunks[index]!
    let shard := chunk.shardId
    let isNew := chunk.isNewChunk v.height
    -- the receipts of the previous chunks must hash to the root the chunk header commits to
    if let some (.full own) := sent[index]! then
      let groups ← groupByShard layout own
      let (root, _) := merklize (← receiptHashes layout groups)
      unless root == chunk.prevOutgoingReceiptsRoot do
        throw
            s!"shard {shard}: the outgoing receipts of the previous chunk do not match prev_outgoing_receipts_root"
    -- a shard that is not tracked, or whose synced state starts later, has no chunk applied here
    if let some tracked := p.tracked then
      unless tracked.contains shard do
        continue
    let mut start? : Option ShardStart := none
    if !pr.roots.contains shard then
      let some s := pr.starts[shard]? | throw s!"no state for shard {shard}"
      if v.height < s.height then
        continue
      unless v.height == s.height && isNew do
        throw s!"shard {shard}: its synced state starts at height {s.height}, not at this block"
      start? := some s
      pr :=
        { pr with
          roots := pr.roots.insert shard s.root, starts := pr.starts.erase shard }
    let some root := pr.roots[shard]? | throw s!"no state for shard {shard}"
    let src := pr.tables.nodeSource (shardKey layout shard)
    let prevExtra? := pr.extras[(v.prevHash.bytes, shard)]?
    let expectedRoot :=
      if isNew then chunk.prevStateRoot
      else
        match prevExtra? with
        | some (.v5 e) => e.stateRoot
        | _ => root
    unless root == expectedRoot do
      throw
          s!"shard {shard}: state root {hex root.bytes} but the chunk header says {hex expectedRoot.bytes}"
    let b := body shard
    if isNew then
      let (txRoot, _) := merklize b.transactions
      unless txRoot == chunk.txRoot do
        throw s!"shard {shard}: the transactions do not hash to the chunk's tx_root"
    let entries ← timed prof "trie-read" fun _ => trieEntries src root
    -- the receipts of this block, then those delivered since the shard's previous chunk
    let mut delivered := incoming[(layout.getShardIndex shard).getD 0]!
    if let some s := start? then
      -- the receipts the state header delivered with the first chunk, which also says what this
      -- block delivered
      if let some (_, mine) := s.incoming.find? (·.1 == hash) then
        unless mine == delivered do
          throw s!"shard {shard}: the receipts of the state sync header differ from the block's"
      delivered := s.delivered
    else if isNew then
      let some prevChunk := prevRec.chunks[index]? | throw "previous chunk missing"
      let mut cur := prevRec
      for _ in [0:100000] do
        if cur.view.height ≤ prevChunk.heightIncluded then
          break
        delivered := delivered ++ ((pr.incoming[(cur.hash.bytes, shard)]?).getD #[])
        cur ← lifted (st.block cur.view.prevHash)
    let pending ←
      (if isNew then delivered else #[]).mapM fun r =>
          match Codec.decodeAll (α := Receipt) r with
          | .ok r => pure r
          | .error e => throw s!"receipt does not decode: {repr e}"
    let update ←
      lifted
          (Epoch.validatorAccountsUpdate p.setup st v.prevHash shard
            (if isNew then chunk.prevValidatorProposals
            else
              match prevExtra? with
              | some (.v5 e) => e.validatorProposals
              | _ => #[]))
    let ctx := chunkContext p v epoch prevRec chunk layout provider update input
    let (prepared, cache) ←
      timed prof "decode-state" fun _ =>
          prepare entries (if isNew then b.transactions else #[]) pending
            (if isNew then b.claimedOutgoing else #[]) ctx pr.cache
    pr := { pr with cache }
    let roundTrip ←
      if p.roundTrip then
        timed prof "round-trip" fun _ => do
            let reencoded ← reencode p.cfg prepared
            let originalMap : Std.HashMap (List UInt8) (List UInt8) :=
              entries.foldl (fun m (k, v) => m.insert k.toList v.toList) {}
            pure
                (decide (reencoded.length = entries.size) &&
                  reencoded.all fun (k, v) => originalMap[k]? == some v)
      else
        pure true
    let (newEntries, extra, outgoing, outcomes, yielded, changeLog) ←
      if isNew then
        do
          let mut overlay : Option Near.TrieOverlay.State := none
          if ctx.update.isNone then
            let (o, cache) ← timed prof "trie-witness" fun _ => overlayOf src root entries pr.cache
            pr := { pr with cache }
            overlay := some o
          let result ← runChunk prof p.cfg p.congestion ctx prepared overlay pr.cache
          -- the next chunks meet the code this one's contracts deployed from their memory in the state
          pr :=
            { pr with
              cache :=
                { pr.cache with
                  byLabel :=
                    result.learned.foldl (fun m e => m.insert e.code.hash e) pr.cache.byLabel } }
          let (outcomeRoot, _) := merklizeHashes (result.outcomes.map (·.leafHash))
          pure
              (result.entries,
                (ChunkExtra.v5
                  { stateRoot := root, outcomeRoot, validatorProposals := result.proposals,
                    gasUsed := result.gasBurnt.toUInt64, gasLimit := chunk.gasLimit,
                    balanceBurnt := ⟨result.balanceBurnt⟩, congestionInfo := result.congestion,
                    bandwidthRequests := result.requests, proposedSplit := none }),
                result.outgoing, result.outcomes, result.yielded, result.changes)
      else
        do
          let (entries, changeLog) ←
            timed prof "run/old-chunk" fun _ => runOldChunk p.cfg p.congestion ctx prepared
          let some (.v5 old) := prevExtra? | throw "no chunk extra before an old chunk"
          pure (entries, ChunkExtra.v5 old, #[], #[], #[], changeLog)
    let oldMap := entryMap entries
    let newMap := entryMap newEntries
    let diff := diffEntries entries newEntries oldMap newMap
    let changes ←
      timed prof "trie-update" fun _ => do
          pure (← Near.Node.Trie.update src root diff).changes
    -- the chunk's commits as `RawStateChangesWithTrieKey`; an entry that differs and the log did not list is a fault of the log
    let missed := missedKeys diff changeLog
    if !missed.isEmpty then
      let describe (k : ByteArray) : String :=
        match TrieKey.parse? k with
        | some (.account a) => s!"account {a.val}"
        | some (.contractCode a) => s!"code {a.val}"
        | some (.accessKey a _) => s!"access key {a.val}"
        | some (.contractData a d) => s!"data {a.val} {hex d}"
        | some _ => "other"
        | none => "unparsed"
      IO.eprintln
          s!"warning: the state change log of shard {shard} at {v.height} missed {missed.size} changed key(s): {(missed.toList.take 6).map describe}"
    let extra : ChunkExtra :=
      match extra with
      | .v5 e => .v5 { e with stateRoot := changes.newRoot }
      | e => e
    let shardOps : Array Store.Op :=
      Store.trieInsertOps (shardKey layout shard) changes ++
        #[.set .chunkExtra (blockShardKey hash layout shard) (Codec.encode extra),
          .set .outgoingReceipts (blockShardKey hash layout shard) (Codec.encode outgoing),
          .set .trieChanges (blockShardKey hash layout shard) (Store.changesBytes changes)] ++
        (if changeLog.isEmpty then #[]
        else
          #[.set .stateChanges (blockShardKey hash layout shard)
              (Near.Node.Chain.stateChangesBytes changeLog)])
    ops := ops ++ shardOps
    pr :=
      { pr with
        tables := shardOps.foldl Store.Tables.apply pr.tables,
        roots := pr.roots.insert shard changes.newRoot,
        outgoing := pr.outgoing.insert (hash.bytes, shard) outgoing,
        extras := pr.extras.insert (hash.bytes, shard) extra }
    reports :=
      reports.push
        { shard, extra, incoming := if isNew then delivered else #[], outgoing, roundTrip, outcomes,
          yielded }
  -- what the block delivers to each shard stays until the shard has a chunk again
  for i in [0:layout.numShards.toNat] do
    let some shard := layout.getShardId i | throw "shard index out of range"
    -- a partial chunk says nothing of the shards it has no proof for
    let known :=
      sent.all fun
        | some (.toShards gs) => gs.any (·.1 == shard)
        | _ => true
    unless known do
      continue
    let op : Store.Op :=
      .set .incomingReceipts (blockShardKey hash layout shard) (Codec.encode incoming[i]!)
    ops := ops.push op
    pr :=
      { pr with
        tables := Store.Tables.apply pr.tables op,
        incoming := pr.incoming.insert (hash.bytes, shard) incoming[i]! }
  return (pr, reports, ops)

end Near.Node.Apply
