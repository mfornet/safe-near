import NearNode.Chain.Genesis

/-!
# The chain store

What the node keeps in the store (`NearNode.Store`, M4) after each block, in one commit with the
trie nodes of the chunks it applied: the block and its header, the epoch manager's `BlockInfo`, the
block merkle tree, the `EpochInfo` of an epoch that was finalized, the `ChunkExtra` and the outgoing
receipts of every shard, and the heads (`HEAD`, `HEADER_HEAD`, `FINAL_HEAD`, `GENESIS_HASH`). `load`
rebuilds the chain state and the progress from a store, so that a restarted node continues with the
next block.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Store

def headKey : ByteArray :=
  "HEAD".toUTF8

def headerHeadKey : ByteArray :=
  "HEADER_HEAD".toUTF8

def finalHeadKey : ByteArray :=
  "FINAL_HEAD".toUTF8

def genesisHashKey : ByteArray :=
  "GENESIS_HASH".toUTF8

/-- `Tip::from_header`. -/
def tipOf (r : BlockRec) : Tip :=
  { height := r.view.height, lastBlockHash := r.hash, prevBlockHash := r.view.prevHash,
    epochId := r.view.epochId, nextEpochId := r.view.nextEpochId }

/-- The operations that store an accepted block. -/
def blockOps (b : Block) (r : BlockRec) : Array Op :=
  #[.set .blockHeader r.hash.bytes (Codec.encode b.header),
    .set .block r.hash.bytes (Codec.encode b),
    .set .blockInfo r.hash.bytes (Codec.encode (BlockInfo.v4 r.info)),
    .set .blockMerkleTree r.hash.bytes (Codec.encode r.tree)]

/-- The operations that store an epoch. -/
def epochOps (id : ByteArray) (e : EpochData) : Array Op :=
  #[.set .epochInfo id (Codec.encode (e.info, e.layout))]

/-- The heads after accepting `r`. -/
def headOps (st : Near.Node.Chain.ChainState) (r : BlockRec) : Array Op :=
  let final := (st.blocks[r.view.lastFinalBlock.bytes]?).getD (st.blocks[st.genesisHash.bytes]!)
  #[.set .blockMisc headKey (Codec.encode (tipOf r)),
    .set .blockMisc headerHeadKey (Codec.encode (tipOf r)),
    .set .blockMisc finalHeadKey (Codec.encode (tipOf final))]

/-- The commit that creates a chain: genesis block, epochs, state and chunk extras. -/
def genesisOps (genesis : Block) (r : BlockRec) (zero : BlockRec)
    (epochs : Array (ByteArray × EpochData)) (trieOps : Array Op)
    (extras : Array (ByteArray × ChunkExtra)) : Array Op :=
  blockOps genesis r ++
    #[.set .blockInfo CryptoHash.zero.bytes (Codec.encode (BlockInfo.v4 zero.info)),
      .set .blockMisc genesisHashKey r.hash.bytes] ++
    epochs.foldl (fun ops (id, e) => ops ++ epochOps id e) #[] ++
    trieOps ++
    extras.map (fun (k, e) => Op.set .chunkExtra k (Codec.encode e)) ++
    #[.set .blockMisc headKey (Codec.encode (tipOf r)),
      .set .blockMisc headerHeadKey (Codec.encode (tipOf r)),
      .set .blockMisc finalHeadKey (Codec.encode (tipOf r))]

/-- Everything a block adds to the store, from the chain state after the block and the chunk
operations. -/
def commitOps (st : Near.Node.Chain.ChainState) (b : Block) (fin : Option Epoch.Finalized)
    (chunkOps : Array Op) : Except String (Array Op) := do
  let some r := st.blocks[b.header.hash.bytes]? | throw "block not recorded"
  let epochs :=
    match fin with
    | some f => epochOps f.epochId.hash.bytes f.data
    | none => #[]
  pure (blockOps b r ++ epochs ++ chunkOps ++ headOps st r)

private def keys (t : Tables) (c : Col) : Array ByteArray :=
  (t.plain[c.id.toNat]!).fold (fun acc k _ => acc.push k) #[]

private def decodeAs (α : Type) [Codec α] (what : String) (b : ByteArray) : Except String α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => pure a
  | .error e => throw s!"{what} does not decode: {repr e}"

/-- Rebuild the chain state and the progress from the content of a store; `none` for a store
that holds no chain. -/
def load (config : Config) (t : Tables) :
    Except String (Option (Near.Node.Chain.ChainState × Progress)) := do
  let some genesisHash := t.get .blockMisc genesisHashKey | return none
  let some headBytes := t.get .blockMisc headKey | return none
  let head ← decodeAs Tip "head" headBytes
  let mut blocks : Std.HashMap ByteArray BlockRec := {}
  let mut genesisChunks : Array ShardChunkHeader := #[]
  for h in keys t .blockInfo do
    let some infoBytes := t.get .blockInfo h | continue
    let .v4 info ← decodeAs BlockInfo "BlockInfo" infoBytes | throw "BlockInfo is not V4"
    if h == CryptoHash.zero.bytes then
      blocks :=
        blocks.insert h
          { hash := CryptoHash.zero, header := default, view := default, chunks := #[], info,
            tree := default }
      continue
    let some blockBytes := t.get .block h | throw "block missing"
    let block ← decodeAs Block "block" blockBytes
    let some v := block.header.view? | throw "header version"
    let some treeBytes := t.get .blockMerkleTree h | throw "block merkle tree missing"
    let tree ← decodeAs PartialMerkleTree "block merkle tree" treeBytes
    blocks :=
      blocks.insert h
        { hash := ⟨h⟩, header := block.header, view := v, chunks := block.chunks, info, tree }
    if h == genesisHash then
      genesisChunks := block.chunks
  let mut epochs : Std.HashMap ByteArray EpochData := {}
  for k in keys t .epochInfo do
    let some b := t.get .epochInfo k | continue
    let (info, layout) ← decodeAs (EpochInfo × ShardLayout) "EpochInfo" b
    epochs := epochs.insert k { info, layout }
  let st : Near.Node.Chain.ChainState :=
    { config, epochs, blocks, head := head.lastBlockHash, headHeight := head.height,
      genesisHash := ⟨genesisHash⟩, genesisChunks }
  -- the state of the shards after the head
  let some headRec := blocks[head.lastBlockHash.bytes]? | throw "head block missing"
  let some epoch := epochs[headRec.info.epochId.hash.bytes]? | throw "epoch of the head missing"
  let mut pr : Progress := { tables := t }
  for c in headRec.chunks do
    let key := blockShardKey head.lastBlockHash epoch.layout c.shardId
    let some extraBytes := t.get .chunkExtra key | throw "chunk extra of the head missing"
    let extra ← decodeAs ChunkExtra "ChunkExtra" extraBytes
    let some outBytes := t.get .outgoingReceipts key | throw "outgoing receipts of the head missing"
    let outgoing ← decodeAs (Array ByteArray) "outgoing receipts" outBytes
    let .v5 e := extra | throw "ChunkExtra is not V5"
    pr :=
      { pr with
        roots := pr.roots.insert c.shardId e.stateRoot,
        extras := pr.extras.insert (head.lastBlockHash.bytes, c.shardId) extra,
        outgoing := pr.outgoing.insert (head.lastBlockHash.bytes, c.shardId) outgoing }
  -- the receipts that chunks sent, which a shard's next chunk after a missing one carries
  for k in keys t .outgoingReceipts do
    let some b := t.get .outgoingReceipts k | continue
    let receipts ← decodeAs (Array ByteArray) "outgoing receipts" b
    let shard := (k.extract 36 40).toList.foldr (fun x acc => acc * 256 + x.toNat) 0
    pr := { pr with outgoing := pr.outgoing.insert (k.extract 0 32, shard.toUInt64) receipts }
  -- the receipts delivered to shards since their last chunk
  for k in keys t .incomingReceipts do
    let some b := t.get .incomingReceipts k | continue
    let receipts ← decodeAs (Array ByteArray) "incoming receipts" b
    let shard := (k.extract 36 40).toList.foldr (fun x acc => acc * 256 + x.toNat) 0
    pr := { pr with incoming := pr.incoming.insert (k.extract 0 32, shard.toUInt64) receipts }
  return some (st, pr)

end Near.Node.Apply
