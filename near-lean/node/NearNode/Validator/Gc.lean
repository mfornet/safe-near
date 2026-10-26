import NearNode.Validator.Persist

/-!
# Garbage collection

`chain/chain/src/garbage_collection.rs` at the pin (`clear_old_blocks_data`, `clear_block_data`, `gc_trie_changes`) and
`get_gc_stop_height_impl` (`runtime/mod.rs`), for the data a validator keeps.

* **What stays.** The blocks from the start of the oldest of the last `gc_num_epochs_to_keep` epochs (default 5) on:
  `gc_stop_height` is that height, and the heights below it are collected, at most `gc_blocks_limit` (2) at a time.
* **Canonical blocks.** Collecting the block `B` at a height applies its trie deletions (`ShardTries::apply_deletions`: the
  references its update took away, which only the states before `B` needed) and deletes the data of its parent: the block, its
  header, its `BlockInfo`, its merkle tree, the chunk extras, the receipts in and out, the chunk bodies, the execution
  outcomes, the receipts and the transactions it indexed. The block at the height itself stays, with its complete state, and
  its parent's state is gone: the tail is the oldest state that can be read.
* **Forks.** A block at the height that is not an ancestor of the tip takes back what its update added
  (`revert_insertions`) and goes with all its data.
* **Refcounts.** The trie nodes are reference counted by hash and shard (`rcAdd`), so a node that a retained state still uses
  survives the deletions of an older block. The changes are kept in the `TrieChanges` column with every block.

Everything one pass deletes is one store commit with the new tail (`TAIL`), so a restart continues from the tail it finds. The
operations also go to the progress' view of the tables, and the maps of the state lose the same blocks. It runs between two
applications (never while a block is being applied on a snapshot of the state, which it would otherwise overwrite).
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Apply Near.Node.Borsh Near.Node.Store

/-- `gc_num_epochs_to_keep`. -/
def defaultEpochsToKeep : Nat :=
  5

/-- `gc_blocks_limit`. -/
def gcBlocksLimit : Nat :=
  2

/-- `get_gc_stop_height_impl`: the height of the first block of the epoch `keep - 1` epochs before the one of `head`. -/
def gcStopHeight (st : CS) (head : CryptoHash) (keep : Nat) : Result BlockHeight := do
  let headRec ← st.block head
  let mut first ← st.block headRec.info.epochFirstBlock
  let mut start := first.info.height
  let mut lastPrev := first.info.prevHash
  for _ in [0:keep - 1] do
    let prev ← st.block lastPrev
    first ← st.block prev.info.epochFirstBlock
    start := first.info.height
    lastPrev := first.info.prevHash
  return start

/-- The blocks of the chain state at a height. -/
def blocksAt (st : CS) (height : BlockHeight) : Array BlockRec :=
  st.blocks.fold
    (fun acc _ r =>
      if r.view.height == height && r.hash != CryptoHash.zero then acc.push r else acc)
    #[]

/-- How a block's trie changes are taken back. -/
inductive GcMode where
  /-- On the canonical chain: the references its update removed. -/
  | canonical
  /-- On a fork: the references its update added. -/
  | fork
  deriving BEq

/-- The operations that take back a block's trie changes, and remove the record of them. -/
def VState.trieOps (s : VState) (r : BlockRec) (mode : GcMode) : Array Op :=
  match s.st.epoch r.info.epochId with
  | .error _ => #[]
  | .ok data =>
    data.layout.shardIds.foldl
      (fun ops shard =>
        let key := blockShardKey r.hash data.layout shard
        let ops :=
          match (s.pr.tables.get .trieChanges key).bind changesOfBytes? with
          | some (insertions, deletions) =>
            ops ++
              deleteOpsOfRefs (shardKey data.layout shard)
                (if mode == GcMode.canonical then deletions else insertions)
          | none => ops
        ops.push (.delete .trieChanges key))
      #[]

/-- Takes a block out of the store and of the memory: the operations, and the state without it. -/
def VState.dropBlock (s : VState) (r : BlockRec) : Array Op × VState :=
  Id.run do
    let hash := r.hash
    let mut ops : Array Op :=
      #[.delete .block hash.bytes, .delete .blockHeader hash.bytes, .delete .blockInfo hash.bytes,
        .delete .blockMerkleTree hash.bytes]
    let mut s := s
    if let .ok data := s.st.epoch r.info.epochId then
      for shard in data.layout.shardIds do
        let key := blockShardKey hash data.layout shard
        ops :=
          ops ++
            #[.delete .chunkExtra key, .delete .outgoingReceipts key, .delete .incomingReceipts key,
              .delete .trieChanges key, .delete .stateChanges key,
              .delete .delivered (deliveredKey hash shard)]
        s :=
          { s with
            pr :=
              { s.pr with
                extras := s.pr.extras.erase (hash.bytes, shard),
                outgoing := s.pr.outgoing.erase (hash.bytes, shard),
                incoming := s.pr.incoming.erase (hash.bytes, shard) },
            deliveredAt := s.deliveredAt.erase (hash.bytes, shard) }
    -- the chunks this block introduced
    for c in r.chunks do
      if c.isNewChunk r.view.height then
        let k := c.chunkHash.hash.bytes
        ops := ops.push (.delete .chunkBody k)
        if s.endorsed.contains k then
          ops := ops.push (.delete .blockMisc (endorsedKey k))
        s :=
          { s with
            chunks := s.chunks.erase k, bodies := s.bodies.erase k, endorsed := s.endorsed.erase k }
    -- what the RPC serves of it: the outcomes it produced, their receipts, the transactions it included
    let outcomeIds :=
      s.outcomes.fold
        (fun acc k o => if o.block == hash then acc.push (k, o.outcome.id.bytes) else acc) #[]
    for (k, receiptId) in outcomeIds do
      ops := ops.push (.delete .outcome k)
      s := { s with outcomes := s.outcomes.erase k }
      if s.receiptsById.contains receiptId then
        ops := ops.push (.delete .receipt receiptId)
        s := { s with receiptsById := s.receiptsById.erase receiptId }
    let txs := s.txIndex.fold (fun acc k (b, _) => if b == hash then acc.push k else acc) #[]
    for k in txs do
      ops := ops.push (.delete .txIndex k)
      s := { s with txIndex := s.txIndex.erase k }
    s :=
      { s with
        st := { s.st with blocks := s.st.blocks.erase hash.bytes },
        blocks := s.blocks.erase hash.bytes, applied := s.applied.erase hash.bytes,
        pending := s.pending.filter (· != hash),
        canon :=
          if s.canon[r.view.height]? == some hash.bytes then s.canon.erase r.view.height
          else s.canon }
    return (ops, s)

/-- Collects the height `height`, below the stop height: the operations, and the state afterwards. -/
def VState.collectHeight (s : VState) (height : BlockHeight) : Array Op × VState :=
  Id.run do
    let onChain := (ancestorAt s.st s.tip height).toOption.map (·.hash)
    let mut ops : Array Op := #[]
    let mut s := s
    for r in blocksAt s.st height do
      if onChain == some r.hash then
        -- the canonical block: its deletions, and the data of its parent
        ops := ops ++ s.trieOps r GcMode.canonical
        if r.view.prevHash != s.st.genesisHash && r.view.prevHash != CryptoHash.zero then
          if let some parent := s.st.blocks[r.view.prevHash.bytes]? then
            if parent.view.height > s.st.config.genesisHeight then
              let (more, s') := s.dropBlock parent
              ops := ops ++ more
              s := s'
      else
        -- a fork: its insertions go, and the block with them
        ops := ops ++ s.trieOps r GcMode.fork
        let (more, s') := s.dropBlock r
        ops := ops ++ more
        s := s'.bump "gcForkBlocks"
    -- no approval, witness or chunk of a height that is collected is of use any more
    for (shard, h) in s.producedChunks.toList do
      if h ≤ height then
        ops := ops.push (.delete .blockMisc (producedChunkKey h shard))
    s :=
      { s with
        witnesses := s.witnesses.filter fun _ w => w.key.heightCreated > height,
        producedChunks := s.producedChunks.filter fun (_, h) => h > height }
    return (ops.push (.set .blockMisc tailKey (u64Bytes height)), { s with tail := height })

/-- The pass: the heights from the tail to the stop height, at most `gcBlocksLimit` blocks at a time (more when far
behind, as a restarted node with a long history). Between two applications only. -/
def Env.collectGarbage (e : Env) : IO Unit := do
  let s ← e.get
  if e.gcEpochs == 0 then
    return
  match gcStopHeight s.st s.tip e.gcEpochs with
  | .error _ =>
    return
  | .ok stop =>
    if stop ≤ s.tail + 1 then
      return
    let limit := max gcBlocksLimit ((stop - s.tail).toNat / 8)
    let mut done := 0
    let mut height := s.tail + 1
    while height < stop && done < limit do
      let s ← e.get
      let (ops, s') := s.collectHeight height
      -- the same operations on the progress' view of the tables, then the store
      let tables := ops.foldl Store.Tables.apply s'.pr.tables
      e.state.set { s' with pr := { s'.pr with tables } }
      e.commit ops
      e.bump "gcHeights"
      done := done + 1
      height := height + 1

/-- Drops the contract code the retained tries no longer reference from the code cache (`CodeCache.prune`). A code is
referenced while a `State` entry of some shard holds a value of its hash with a positive count; garbage collection takes
those counts back with the blocks. The scan of the entries is done when the cache has doubled since the last pruning.
Between two applications only, like `collectGarbage`: an application replaces the progress, cache included. -/
def Env.pruneCodes (e : Env) : IO Unit := do
  let s ← e.get
  if s.pr.cache.byLabel.size < s.pr.cache.pruneAt then
    return
  let live : Std.HashSet ByteArray :=
    s.pr.tables.rc.fold
      (fun acc k (d, n) =>
        if n > 0 && k.size == 40 && d.size > 32 then acc.insert (k.extract 8 40) else acc)
      s.keepCodes
  let before := s.pr.cache.byLabel.size
  let cache := s.pr.cache.prune live fun l => (hashOfLabel? l).map fun b => ⟨b.toArray⟩
  e.state.set { s with pr := { s.pr with cache } }
  e.bumpBy "codesPruned" (before - cache.byLabel.size)

end Near.Node.Validator
