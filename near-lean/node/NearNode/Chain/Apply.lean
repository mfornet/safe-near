import NearNode.Chain.ApplyChunk
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

/-- The parameters of the chain. -/
structure Params where
  setup : Epoch.Setup
  cfg : Wasm.Near.RuntimeConfig
  congestion : Near.Congestion.Config
  protocol : Nat
  chainId : String

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

/-- The result of one chunk. -/
structure ShardReport where
  shard : UInt64
  extra : ChunkExtra
  incoming : Array ByteArray
  outgoing : Array ByteArray
  /-- Whether the conversion of the pre-state encoded back to the trie's entries. -/
  roundTrip : Bool
  outcomes : Array ExecutionOutcomeWithId := #[]

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

/-- The new root and changes that turn the entries `old` of the trie at `root` into `new`. -/
def updateTrie (src : NodeSource) (root : CryptoHash) (old new : Array (ByteArray × ByteArray)) :
    Except String TrieChanges := do
  let oldMap : Std.HashMap ByteArray ByteArray := old.foldl (fun m (k, v) => m.insert k v) {}
  let newMap : Std.HashMap ByteArray ByteArray := new.foldl (fun m (k, v) => m.insert k v) {}
  let mut changes : Array Change := #[]
  for (k, v) in new do
    if oldMap[k]? != some v then
      changes := changes.push (k, some v)
  for (k, _) in old do
    if !newMap.contains k then
      changes := changes.push (k, none)
  pure (← update src root changes).changes

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

/-- The receipts every shard is delivered by a block (`collect_incoming_receipts_from_chunks`): each
new chunk contributes the receipts its previous chunk sent, grouped by receiving shard, and the
contributions to a shard are shuffled with the previous block's hash as the seed. `sent` has an entry
for every chunk of the block (index order) and `none` for a chunk that is not new. -/
def incomingReceipts (layout : ShardLayout) (prevHash : CryptoHash)
    (sent : Array (Option (Array ByteArray))) : Except String (Array (Array ByteArray)) := do
  let grouped ← sent.filterMapM fun s => s.mapM (groupByShard layout)
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

/-! ### Applying a block -/

/-- Apply the chunks of an accepted block. `body shard` is the chunk's body. Returns the progress,
a report per shard and the store operations of the block. -/
def applyBlock (p : Params) (st : Near.Node.Chain.ChainState) (block : Block) (body : UInt64 → Body)
    (pr : Progress) : Except String (Progress × Array ShardReport × Array Store.Op) := do
  let hash := block.header.hash
  let some v := block.header.view? | throw "header version"
  let rec_ ← st.block hash |>.mapError (·.kind)
  let epochId := rec_.info.epochId
  let epoch ← st.epoch epochId |>.mapError (·.kind)
  let layout := epoch.layout
  let prevRec ← st.block v.prevHash |>.mapError (·.kind)
  -- what the previous chunk of each new chunk sent: the receipts of the block that included it
  let mut sent : Array (Option (Array ByteArray)) := #[]
  for index in [0:block.chunks.size] do
    let c := block.chunks[index]!
    if c.isNewChunk v.height then
      let some prevChunk := prevRec.chunks[index]? | throw "previous chunk missing"
      let included ← blockAtHeight st prevRec prevChunk.heightIncluded
      match pr.outgoing[(included.hash.bytes, c.shardId)]? with
      | some r =>
        sent := sent.push (some r)
      | none =>
        throw s!"no outgoing receipts of shard {c.shardId} at height {prevChunk.heightIncluded}"
    else
      sent := sent.push none
  let incoming ← incomingReceipts layout v.prevHash sent
  let provider ← providerOf p st v.prevHash epochId |>.mapError (·.kind)
  let input ← schedulerInput block layout v.prevHash
  let mut pr := pr
  let mut reports : Array ShardReport := #[]
  let mut ops : Array Store.Op := #[]
  for index in [0:block.chunks.size] do
    let chunk := block.chunks[index]!
    let shard := chunk.shardId
    let isNew := chunk.isNewChunk v.height
    -- the receipts of the previous chunks must hash to the root the chunk header commits to
    if let some own := sent[index]! then
      let groups ← groupByShard layout own
      let (root, _) := merklize (← receiptHashes layout groups)
      unless root == chunk.prevOutgoingReceiptsRoot do
        throw
            s!"shard {shard}: the outgoing receipts of the previous chunk do not match prev_outgoing_receipts_root"
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
    let entries ← trieEntries src root
    -- the receipts of this block, then those delivered since the shard's previous chunk
    let mut delivered := incoming[(layout.getShardIndex shard).getD 0]!
    if isNew then
      let some prevChunk := prevRec.chunks[index]? | throw "previous chunk missing"
      let mut cur := prevRec
      for _ in [0:100000] do
        if cur.view.height ≤ prevChunk.heightIncluded then
          break
        delivered := delivered ++ ((pr.incoming[(cur.hash.bytes, shard)]?).getD #[])
        cur ← (st.block cur.view.prevHash |>.mapError (·.kind))
    let pending ←
      (if isNew then delivered else #[]).mapM fun r =>
          match Codec.decodeAll (α := Receipt) r with
          | .ok r => pure r
          | .error e => throw s!"receipt does not decode: {repr e}"
    let update ←
      (Epoch.validatorAccountsUpdate p.setup st v.prevHash shard
            (if isNew then chunk.prevValidatorProposals
            else
              match prevExtra? with
              | some (.v5 e) => e.validatorProposals
              | _ => #[]) |>.mapError
          (·.kind))
    let ctx : ChunkContext :=
      { protocol := p.protocol, height := v.height.toNat, timestamp := v.timestamp.toNat,
        epochHeight := epoch.info.view.epochHeight, gasPrice := prevRec.view.nextGasPrice.val,
        gasLimit := chunk.gasLimit.toNat, randomSeed := v.randomValue.bytes.toList,
        chainId := p.chainId, shardId := shard.toNat,
        shardIds := layout.shardIds.toList.map (·.toNat), epochInfo := provider,
        update := update.map modelUpdate, scheduler := input }
    let (prepared, cache) ←
      prepare entries (if isNew then b.transactions else #[]) pending
          (if isNew then b.claimedOutgoing else #[]) ctx pr.cache
    pr := { pr with cache }
    let reencoded ← reencode p.cfg prepared
    let originalMap : Std.HashMap (List UInt8) (List UInt8) :=
      entries.foldl (fun m (k, v) => m.insert k.toList v.toList) {}
    let roundTrip :=
      reencoded.length == entries.size && reencoded.all fun (k, v) => originalMap[k]? == some v
    let (newEntries, extra, outgoing, outcomes) ←
      if isNew then
        do
          let result ← runChunk p.cfg p.congestion ctx prepared
          let (outcomeRoot, _) := merklizeHashes (result.outcomes.map (·.leafHash))
          pure
              (result.entries,
                (ChunkExtra.v5
                  { stateRoot := root, outcomeRoot, validatorProposals := result.proposals,
                    gasUsed := result.gasBurnt.toUInt64, gasLimit := chunk.gasLimit,
                    balanceBurnt := ⟨result.balanceBurnt⟩, congestionInfo := result.congestion,
                    bandwidthRequests := result.requests, proposedSplit := none }),
                result.outgoing, result.outcomes)
      else
        do
          let entries ← runOldChunk p.cfg p.congestion ctx prepared
          let some (.v5 old) := prevExtra? | throw "no chunk extra before an old chunk"
          pure (entries, ChunkExtra.v5 old, #[], #[])
    let changes ← updateTrie src root entries newEntries
    let extra : ChunkExtra :=
      match extra with
      | .v5 e => .v5 { e with stateRoot := changes.newRoot }
      | e => e
    let shardOps : Array Store.Op :=
      Store.trieInsertOps (shardKey layout shard) changes ++
        #[.set .chunkExtra (blockShardKey hash layout shard) (Codec.encode extra),
          .set .outgoingReceipts (blockShardKey hash layout shard) (Codec.encode outgoing)]
    ops := ops ++ shardOps
    pr :=
      { pr with
        tables := shardOps.foldl Store.Tables.apply pr.tables,
        roots := pr.roots.insert shard changes.newRoot,
        outgoing := pr.outgoing.insert (hash.bytes, shard) outgoing,
        extras := pr.extras.insert (hash.bytes, shard) extra }
    reports :=
      reports.push
        { shard, extra, incoming := if isNew then delivered else #[], outgoing, roundTrip,
          outcomes }
  -- what the block delivers to each shard stays until the shard has a chunk again
  for i in [0:layout.numShards.toNat] do
    let some shard := layout.getShardId i | throw "shard index out of range"
    let op : Store.Op :=
      .set .incomingReceipts (blockShardKey hash layout shard) (Codec.encode incoming[i]!)
    ops := ops.push op
    pr :=
      { pr with
        tables := Store.Tables.apply pr.tables op,
        incoming := pr.incoming.insert (hash.bytes, shard) incoming[i]! }
  return (pr, reports, ops)

end Near.Node.Apply
