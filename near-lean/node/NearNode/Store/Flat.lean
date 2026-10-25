import NearNode.Store.Trie
import NearNode.Primitives.Flat

/-!
# Flat storage

The semantics of nearcore's `FlatStorage` (`core/store/src/flat/storage.rs`, `delta.rs`,
`adapter/flat_store.rs`) for the value lookup, without its threads and locks.

The flat state is the `FlatState` column: `ShardUId ++ trie key` to `FlatStateValue` (the value
itself up to 4000 bytes, a `ValueRef` beyond), as of the *flat head* block. Each later block on a
fork has a *delta*: the keys it changes (`none` deletes), stored as `FlatStateChanges` and
`FlatStateDeltaMetadata` and cached here as references. A lookup at a block collects the blocks
from it back to the flat head (skipping blocks without changes through
`prev_block_with_changes`), takes the answer of the first block that has the key, and otherwise
reads the column. Moving the flat head applies the deltas up to the new head to the column, one
block at a time, and drops them.

Functions take a `Tables` view of the store and return the operations of the change, for the
caller to commit atomically; the cache is a value and is replaced when the commit succeeds.
-/

namespace Near.Node.Store

open Borsh

inductive FlatError where
  | blockNotSupported (head block : CryptoHash)
  | internal (msg : String)
  deriving BEq

def FlatError.toString : FlatError → String
  | .blockNotSupported h b =>
    s!"flat storage with head {hashHex' h} does not support block {hashHex' b}"
  | .internal m => m
where hashHex' (h : CryptoHash) : String := Trie.hashHex h

instance : ToString FlatError :=
  ⟨FlatError.toString⟩

/-- A block's changes as `ValueRef`s by key (`CachedFlatStateChanges`). -/
abbrev CachedChanges :=
  Std.HashMap ByteArray (Option ValueRef)

structure CachedDelta where
  metadata : FlatStateDeltaMetadata
  changes : CachedChanges

/-- One shard's flat storage. -/
structure FlatStorage where
  /-- The `ShardUId` key bytes. -/
  shard : ByteArray
  flatHead : FlatBlockInfo
  deltas : Std.HashMap CryptoHash CachedDelta

namespace FlatStorage

/-- `KeyForFlatStateDelta::to_bytes`. -/
def deltaKey (shard : ByteArray) (block : CryptoHash) : ByteArray :=
  shard ++ block.bytes

/-- `encode_flat_state_db_key`. -/
def stateKey (shard key : ByteArray) : ByteArray :=
  shard ++ key

private def cache (changes : FlatStateChanges) : CachedChanges :=
  changes.foldl (fun m (k, v) => m.insert k (v.map FlatStateValue.toValueRef)) {}

private def decode? [Codec α] (b? : Option ByteArray) : Except FlatError (Option α) :=
  match b? with
  | none => .ok none
  | some b =>
    match Codec.decodeAll (α := α) b with
    | .ok a => .ok (some a)
    | .error e => .error (.internal s!"corrupt flat storage record: {repr e}")

/-- `get_flat_storage_status`. -/
def status (t : Tables) (shard : ByteArray) : Except FlatError FlatStorageStatus := do
  return (← decode? (t.get .flatStorageStatus shard)).getD .empty

/-- `FlatStorage::new`: read the head and the cached deltas of a shard from the store. -/
def load (t : Tables) (shard : ByteArray) : Except FlatError FlatStorage := do
  let .ready head ← status t shard | .error (.internal "flat storage is not ready")
  let mut deltas := {}
  for (k, v) in t.plain[Col.flatStateDeltaMetadata.id.toNat]! do
    if k.size == 40 && k.extract 0 8 == shard then
      let some (m : FlatStateDeltaMetadata) ← decode? (some v) | throw (.internal "empty metadata")
      let changes : CachedChanges ←
        if m.prevBlockWithChanges.isNone then
          match ← decode? (t.get .flatStateChanges k) with
          | some (c : FlatStateChanges) =>
            pure (cache c)
          | none =>
            throw (.internal s!"cannot find block delta for block {Trie.hashHex m.block.hash}")
        else
          pure {}
      deltas := deltas.insert m.block.hash ⟨m, changes⟩
  return ⟨shard, head, deltas⟩

/-- The blocks from `target` (inclusive) back to the flat head (exclusive) whose changes matter, in
backwards order (`get_blocks_to_head`). -/
def blocksToHead (fs : FlatStorage) (target : CryptoHash) : Except FlatError (Array CryptoHash) :=
  do
  let mut blocks := #[]
  let mut block := target
  for _ in [0:fs.deltas.size + 1] do
    if block == fs.flatHead.hash then
      return blocks
    let some d := fs.deltas.get? block
      | throw (.blockNotSupported fs.flatHead.hash target)
    match d.metadata.prevBlockWithChanges with
    | none =>
      blocks := blocks.push block
      block := d.metadata.block.prevHash
    | some p =>
      if block == target then
        blocks := blocks.push block
      block := if p.height > fs.flatHead.height then p.hash else fs.flatHead.hash
  throw (.internal "cycle in the flat storage deltas")

/-- The value of `key` at `block` (`get_value`): `none` if absent. The value of a changed key comes
back as a reference. -/
def getValue (fs : FlatStorage) (t : Tables) (block : CryptoHash) (key : ByteArray) :
    Except FlatError (Option FlatStateValue) := do
  for b in ← fs.blocksToHead block do
    let some d := fs.deltas.get? b
      | throw (.internal s!"delta does not exist for block {Trie.hashHex b}")
    match d.changes.get? key with
    | some v =>
      return v.map FlatStateValue.ref
    | none =>
      pure ()
  decode? (t.get .flatState (stateKey fs.shard key))

/-- `contains_key`. -/
def containsKey (fs : FlatStorage) (t : Tables) (block : CryptoHash) (key : ByteArray) :
    Except FlatError Bool := do
  for b in ← fs.blocksToHead block do
    let some d := fs.deltas.get? b
      | throw (.internal s!"delta does not exist for block {Trie.hashHex b}")
    match d.changes.get? key with
    | some v =>
      return v.isSome
    | none =>
      pure ()
  return (t.get .flatState (stateKey fs.shard key)).isSome

/-- The bytes of a value: inlined, or fetched from the trie's `State` column by hash. -/
def deref (t : Tables) (shard : ByteArray) : FlatStateValue → Option ByteArray
  | .inlined v => some v
  | .ref r => t.get .state (Store.stateKey shard r.hash)

/-- The metadata of the delta of a block with the given changes (`get_prev_block_with_changes`
and `FlatStateDelta`): a block without changes points at the closest earlier block that has some. -/
def deltaMetadata (fs : FlatStorage) (block : FlatBlockInfo) (changes : FlatStateChanges) :
    FlatStateDeltaMetadata :=
  if !changes.isEmpty then ⟨block, none⟩
  else
    match fs.deltas.get? block.prevHash with
    | some d =>
      ⟨block,
        some
          (d.metadata.prevBlockWithChanges.getD ⟨d.metadata.block.hash, d.metadata.block.height⟩)⟩
    | none =>
      if fs.flatHead.hash == block.prevHash then ⟨block, some ⟨block.prevHash, fs.flatHead.height⟩⟩
      else ⟨block, none⟩

/-- `add_delta`: the delta of a new block, which must extend the head or a cached block. -/
def addDelta (fs : FlatStorage) (metadata : FlatStateDeltaMetadata) (changes : FlatStateChanges) :
    Except FlatError (FlatStorage × Array Op) := do
  let block := metadata.block
  if block.prevHash != fs.flatHead.hash && !fs.deltas.contains block.prevHash then
    throw (.blockNotSupported fs.flatHead.hash block.hash)
  let key := deltaKey fs.shard block.hash
  let ops :=
    #[Op.set .flatStateChanges key (Codec.encode changes),
      Op.set .flatStateDeltaMetadata key (Codec.encode metadata)]
  return ({ fs with deltas := fs.deltas.insert block.hash ⟨metadata, cache changes⟩ }, ops)

/-- `BLOCKS_WITH_CHANGES_FLAT_HEAD_GAP`. -/
def headGap : Nat :=
  2

/-- `get_new_flat_head`: unless `strict`, stay two blocks with changes behind `block`. -/
def newFlatHead (fs : FlatStorage) (block : CryptoHash) (strict : Bool) :
    Except FlatError CryptoHash := do
  if strict then
    return block
  let mut newHead := block
  let mut withChanges := 0
  for _ in [0:fs.deltas.size + headGap + 1] do
    if withChanges ≥ headGap then
      return newHead
    if newHead == fs.flatHead.hash then
      return fs.flatHead.hash
    let some d := fs.deltas.get? newHead
      | throw (.blockNotSupported fs.flatHead.hash newHead)
    match d.metadata.prevBlockWithChanges with
    | none =>
      withChanges := withChanges + 1
      if withChanges == headGap then
        return newHead
      newHead := d.metadata.block.prevHash
    | some p =>
      if p.height ≤ fs.flatHead.height then
        return fs.flatHead.hash
      newHead := p.hash
  throw (.internal "cycle in the flat storage deltas")

/-- `update_flat_head`: apply the deltas up to `block` to the column, set the status, and drop the
deltas at or below that height. -/
def updateFlatHead (fs : FlatStorage) (t : Tables) (block : CryptoHash) (strict : Bool := true) :
    Except FlatError (FlatStorage × Array Op) := do
  let target ← fs.newFlatHead block strict
  if target == fs.flatHead.hash then
    return (fs, #[])
  let mut fs := fs
  let mut ops := #[]
  for b in (← fs.blocksToHead target).reverse do
    let key := deltaKey fs.shard b
    let some (changes : FlatStateChanges) ←
      decode?
          (t.get .flatStateChanges
            key) | throw (.internal s!"delta does not exist for block {Trie.hashHex b}")
    let some d := fs.deltas.get? b
      | throw (.internal s!"delta does not exist for block {Trie.hashHex b}")
    for (k, v) in changes do
      ops :=
        ops.push
          (match v with
          | some v => Op.set .flatState (stateKey fs.shard k) (Codec.encode v)
          | none => Op.delete .flatState (stateKey fs.shard k))
    ops :=
      ops.push
        (Op.set .flatStorageStatus fs.shard
          (Codec.encode (FlatStorageStatus.ready d.metadata.block)))
    let height := d.metadata.block.height
    let dropped :=
      fs.deltas.fold (fun acc h x => if x.metadata.block.height ≤ height then acc.push h else acc)
        #[]
    for h in dropped do
      ops :=
        ops ++
          #[Op.delete .flatStateChanges (deltaKey fs.shard h),
            Op.delete .flatStateDeltaMetadata (deltaKey fs.shard h)]
    fs :=
      { fs with
        flatHead := d.metadata.block, deltas := dropped.foldl (·.erase ·) fs.deltas }
  return (fs, ops)

/-- `FlatStateChanges::from_state_changes`: the last change of each key, as stored on disk. -/
def changesOfState (cs : Array RawStateChangesWithTrieKey) : FlatStateChanges :=
  (cs.filterMap fun c =>
        c.trieKey.toVec?.bind fun k =>
          c.changes.back?.map fun ch => (k, ch.data.map FlatStateValue.onDisk)).qsort
    fun a b => compareBytes a.1 b.1 == .lt

/-- `FlatStateChanges::from_raw_key_value`. -/
def changesOfRaw (es : Array (ByteArray × Option ByteArray)) : FlatStateChanges :=
  (es.foldl
        (fun (m : Std.HashMap ByteArray (Option FlatStateValue)) (k, v) =>
          m.insert k (v.map FlatStateValue.onDisk))
        {}).toArray.qsort
    fun a b => compareBytes a.1 b.1 == .lt

/-- The operations that write the flat state of a complete entry set at a head block. -/
def initOps (shard : ByteArray) (head : FlatBlockInfo) (entries : Array (ByteArray × ByteArray)) :
    Array Op :=
  entries.map
      (fun (k, v) =>
        Op.set .flatState (stateKey shard k) (Codec.encode (FlatStateValue.onDisk v))) ++
    #[Op.set .flatStorageStatus shard (Codec.encode (FlatStorageStatus.ready head))]

end FlatStorage

end Near.Node.Store
