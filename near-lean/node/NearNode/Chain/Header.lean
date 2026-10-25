import NearNode.Chain.Validate

/-!
# Headers first, bodies later

The observer syncs the way nearcore's does (`chain/client/src/sync/{header,block,state}`): headers
up to the network head, then the state of a recent epoch, then blocks. A header is accepted as
`Chain::sync_block_headers` accepts it (`validate_header` and, for the epoch manager,
`BlockInfo::from_header`), which needs no chunk. The chain state then holds a record without chunk
headers. A block that arrives later gets its body checked (`attachBody`: everything
`start_process_block_async` checks beyond the header) and its chunk headers attached.

`syncHash` finds the block nearcore syncs the state of an epoch at
(`chain/chain/src/state_sync/utils.rs`, `update_sync_hashes`), and `extraSyncBlocks` the blocks that
must be fetched with it (`Chain::get_extra_sync_block_hashes`).
-/

namespace Near.Node.Chain

open Near.Node Borsh

/-- `Chain::sync_block_headers` for one header: the checks of `validate_header`, then the record
without chunks. -/
def acceptHeader (st : ChainState) (header : BlockHeader) : Result ChainState := do
  let some v := header.view?
    | fail "Unsupported" "header version"
  let hash := header.hash
  guardErr (st.blockExists hash) "BlockKnown"
  -- a header whose parent is not accepted yet is an orphan
  guardErr (!st.blockExists v.prevHash) "DBNotFoundErr" "block header not found"
  guardErr (!st.epochExists v.epochId) "EpochOutOfBounds"
  validateHeader st v hash
  st.record header v #[]

/-- The body of a block whose header was accepted: the block must be the one the header commits to
(`block_body_hash`), and pass the checks `validateBody` lists; its chunk headers are then attached. -/
def attachBody (st : ChainState) (block : Block) : Result ChainState := do
  let some v := block.header.view?
    | fail "Unsupported" "header version"
  let hash := block.header.hash
  let rec_ ← st.block hash
  match block.computeBlockBodyHash with
  | none =>
    fail "InvalidSignature"
  | some bodyHash =>
    guardErr (v.blockBodyHash != bodyHash) "InvalidSignature"
  let epoch ← st.epoch v.epochId
  guardErr (block.chunks.size != epoch.layout.shardIds.size) "IncorrectNumberOfChunkHeaders"
  let prev ← st.block v.prevHash
  validateBody st block v prev
  pure { st with blocks := st.blocks.insert hash.bytes { rec_ with chunks := block.chunks } }

/-- Whether the block's body is attached. -/
def BlockRec.hasBody (r : BlockRec) : Bool :=
  !r.chunks.isEmpty

namespace ChainState

/-- Whether the body of the block is attached. -/
def hasBodyOf (st : ChainState) (h : CryptoHash) : Bool :=
  match st.blocks[h.bytes]? with
  | some r => r.hasBody
  | none => false

end ChainState

/-! ### The block a state is synced at -/

/-- The blocks of the epoch of `tip` from the epoch's first block to `tip`. -/
def epochBlocks (st : ChainState) (tip : CryptoHash) : Result (Array BlockRec) := do
  let t ← st.block tip
  let epoch := t.info.epochId
  let mut out : Array BlockRec := #[t]
  let mut cur := t
  for _ in [0:100000] do
    if cur.info.prevHash == CryptoHash.zero then
      break
    let p ← st.block cur.info.prevHash
    if p.info.epochId != epoch then
      break
    out := out.push p
    cur := p
  pure out.reverse

/-- The new chunks of each shard seen in the epoch up to each block, at most two
(`StateSyncNewChunks`): zero at the first block, then `+1` for each shard whose chunk is new. -/
def newChunkCounts (blocks : Array BlockRec) : Array (Array Nat) :=
  Id.run do
    let mut out : Array (Array Nat) := #[]
    for h : i in [0:blocks.size] do
      let b := blocks[i]
      if i == 0 then
        out := out.push (Array.replicate b.view.chunkMask.size 0)
      else
        let prev := out[i - 1]!
        out :=
          out.push
            ((prev.zip b.view.chunkMask).map fun (n, new) => if new && n < 2 then n + 1 else n)
    return out

/-- The block the state of `tip`'s epoch is synced at: the child of the first block with two new
chunks of every shard in the epoch (`P`), once it is final as seen from `tip`. State sync asks for the
state before `S` and applies the chunks up to `P`. -/
def syncHash (st : ChainState) (tip : CryptoHash) : Result (Option CryptoHash) := do
  let blocks ← epochBlocks st tip
  let counts := newChunkCounts blocks
  let t := blocks.back!
  let some first := blocks[0]? | return none
  -- the epoch must start after the genesis block's own epoch
  if first.info.prevHash == CryptoHash.zero || first.view.prevHeight == st.config.genesisHeight then
    return none
  let enough (i : Nat) : Bool := (counts[i]!).all (· ≥ 2)
  let mut found : Option Nat := none
  for i in [0:blocks.size] do
    if found.isNone && enough i then
      found := some i
  match found with
  | none =>
    pure none
  | some p =>
    if p + 1 ≥ blocks.size then
      return none
    let s := blocks[p + 1]!
    let final ← st.block t.view.lastFinalBlock
    if s.view.height ≤ final.info.height then
      pure (some s.hash)
    else
      pure none

/-- The blocks of the state sync window other than the sync block and its parent: from the parent's
parent down to the lowest height a chunk of the parent was included at
(`Chain::get_extra_sync_block_hashes`). Empty until the parent's body is known. -/
def extraSyncBlocks (st : ChainState) (syncHash : CryptoHash) : Result (Array CryptoHash) := do
  let s ← st.block syncHash
  let p ← st.block s.view.prevHash
  if !p.hasBody then
    return #[]
  let some minIncluded :=
    p.chunks.foldl
      (fun m c =>
        some
          (match m with
          | some x => min x c.heightIncluded
          | none => c.heightIncluded))
      none
    | return #[]
  let mut out := #[]
  let mut cur := p.view.prevHash
  for _ in [0:100000] do
    if cur == CryptoHash.zero then
      break
    let r ← st.block cur
    if r.view.height < minIncluded then
      break
    out := out.push cur
    cur := r.view.prevHash
  pure out

end Near.Node.Chain
