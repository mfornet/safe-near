import NearNode.Store.Crc32
import NearNode.Primitives.Basic

/-!
# Store columns, operations and the log record format

A store holds a few named columns (a subset of nearcore's `DBCol`). A *commit* is a batch of
operations that is applied all together or not at all; on disk it is one self-checking record:

```
"NRCD" | payload length u32 | crc32 of the payload u32 | payload
payload = commit sequence number u64 | operation count u32 | operations
operation = 0 set    column u8 | key (u32 length, bytes) | value (u32 length, bytes)
          | 1 delete column u8 | key
          | 2 rcAdd  column u8 | key | data (u32 length, bytes) | delta i64
```
-/

namespace Near.Node.Store

/-- The columns, after nearcore's `DBCol`; the numbers are this store's own. -/
inductive Col where
  /-- Trie nodes and values by `ShardUId ++ hash`, reference counted (`DBCol::State`). -/
  | state
  /-- The flat state, `ShardUId ++ trie key` to `FlatStateValue` (`DBCol::FlatState`). -/
  | flatState
  /-- The changes of one block to the flat state (`DBCol::FlatStateChanges`). -/
  | flatStateChanges
  /-- The metadata of one block's changes (`DBCol::FlatStateDeltaMetadata`). -/
  | flatStateDeltaMetadata
  /-- The flat storage status of a shard (`DBCol::FlatStorageStatus`). -/
  | flatStorageStatus
  /-- Head pointers and other named values (`DBCol::BlockMisc`). -/
  | blockMisc
  /-- The post-state of a chunk (`DBCol::ChunkExtra`). -/
  | chunkExtra
  /-- Block headers by block hash (`DBCol::BlockHeader`). -/
  | blockHeader
  /-- Blocks by block hash (`DBCol::Block`). -/
  | block
  /-- The epoch manager's `BlockInfo` by block hash (`DBCol::BlockInfo`). -/
  | blockInfo
  /-- `EpochInfo` and its shard layout by epoch id (`DBCol::EpochInfo`). -/
  | epochInfo
  /-- The block merkle tree after each block (`DBCol::BlockMerkleTree`). -/
  | blockMerkleTree
  /-- The receipts a chunk sent, by block hash and shard (`DBCol::OutgoingReceipts`). -/
  | outgoingReceipts
  /-- The receipts a block delivers to a shard, by block hash and shard (`DBCol::IncomingReceipts`). -/
  | incomingReceipts
  /-- The bodies of the chunks blocks included, by chunk hash (`DBCol::Chunks`). -/
  | chunkBody
  /-- Execution outcomes with their proofs, by transaction hash or receipt id (`DBCol::TransactionResultForBlock`). -/
  | outcome
  /-- Receipts by receipt id (`DBCol::Receipts`). -/
  | receipt
  /-- The block and chunk that included a transaction, by transaction hash. -/
  | txIndex
  /-- The receipts a chunk applied at a block and shard, in order, by block hash and shard. -/
  | delivered
  /-- The reference count changes of the trie of one chunk, by block hash and `ShardUId`
  (`DBCol::TrieChanges`): what garbage collection takes back (`Store/Trie.lean`). -/
  | trieChanges
  deriving BEq, Inhabited, Repr

namespace Col

def id : Col → UInt8
  | .state => 0
  | .flatState => 1
  | .flatStateChanges => 2
  | .flatStateDeltaMetadata => 3
  | .flatStorageStatus => 4
  | .blockMisc => 5
  | .chunkExtra => 6
  | .blockHeader => 7
  | .block => 8
  | .blockInfo => 9
  | .epochInfo => 10
  | .blockMerkleTree => 11
  | .outgoingReceipts => 12
  | .incomingReceipts => 13
  | .chunkBody => 14
  | .outcome => 15
  | .receipt => 16
  | .txIndex => 17
  | .delivered => 18
  | .trieChanges => 19

def all : List Col :=
  [.state, .flatState, .flatStateChanges, .flatStateDeltaMetadata, .flatStorageStatus, .blockMisc,
    .chunkExtra, .blockHeader, .block, .blockInfo, .epochInfo, .blockMerkleTree, .outgoingReceipts,
    .incomingReceipts, .chunkBody, .outcome, .receipt, .txIndex, .delivered, .trieChanges]

def ofId? (n : UInt8) : Option Col :=
  all.find? (·.id == n)

/-- `DBCol::is_rc`: the column counts references. -/
def isRc : Col → Bool
  | .state => true
  | _ => false

end Col

/-- One operation of a commit. -/
inductive Op where
  | set (col : Col) (key value : ByteArray)
  | delete (col : Col) (key : ByteArray)
  /-- Add `delta` references to a reference counted entry, with its data when it is added. -/
  | rcAdd (col : Col) (key data : ByteArray) (delta : Int)

def le32 (d : ByteArray) (x : Nat) : ByteArray :=
  d.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

def le64 (d : ByteArray) (x : UInt64) : ByteArray :=
  (List.range 8).foldl (fun d i => d.push (x >>> (8 * i).toUInt64).toUInt8) d

private def putBlob (d b : ByteArray) : ByteArray :=
  (le32 d b.size).append b

/-- Append the encoding of an operation. -/
def Op.encode (d : ByteArray) : Op → ByteArray
  | .set c k v => putBlob (putBlob (d.push 0 |>.push c.id) k) v
  | .delete c k => putBlob (d.push 1 |>.push c.id) k
  | .rcAdd c k data delta =>
    le64 (putBlob (putBlob (d.push 2 |>.push c.id) k) data) (Int64.ofInt delta).toUInt64

/-- The record that carries a commit. -/
def encodeCommit (seq : UInt64) (ops : Array Op) : ByteArray :=
  let payload := ops.foldl Op.encode (le32 (le64 ByteArray.empty seq) ops.size)
  (le32 (le32 "NRCD".toUTF8 payload.size) (crc32 payload).toNat).append payload

/-- A cursor over bytes. -/
structure Reader where
  data : ByteArray
  pos : Nat := 0

abbrev P :=
  StateT Reader (Except String)

def take (n : Nat) : P ByteArray := do
  let r ← get
  if r.pos + n > r.data.size then
    throw "truncated"
  set { r with pos := r.pos + n }
  return r.data.extract r.pos (r.pos + n)

def u8 : P UInt8 := do
  return (← take 1).get! 0

def u32 : P Nat := do
  let b ← take 4
  return (b.get! 0).toNat ||| (b.get! 1).toNat <<< 8 ||| (b.get! 2).toNat <<< 16 |||
      (b.get! 3).toNat <<< 24

def u64 : P UInt64 := do
  let b ← take 8
  return (List.range 8).foldl (fun acc i => acc ||| (b.get! i).toUInt64 <<< (8 * i).toUInt64) 0

def blob : P ByteArray := do
  take (← u32)

def col : P Col := do
  match Col.ofId? (← u8) with
  | some c =>
    return c
  | none =>
    throw "unknown column"

def op : P Op := do
  match ← u8 with
  | 0 =>
    return .set (← col) (← blob) (← blob)
  | 1 =>
    return .delete (← col) (← blob)
  | 2 =>
    let c ← col
    let k ← blob
    let data ← blob
    return .rcAdd c k data (Int64.toInt (Int64.ofUInt64 (← u64)))
  | _ =>
    throw "unknown operation"

/-- Decode a payload: the commit number and its operations. -/
def decodePayload (payload : ByteArray) : Except String (UInt64 × Array Op) := do
  let ((seq, ops), r) ←
    (do
            let seq ← u64
            let n ← u32
            let mut ops := #[]
            for _ in [0:n] do
              ops := ops.push (← op)
            return (seq, ops) : P _).run
        { data := payload }
  if r.pos != payload.size then
    throw "trailing bytes in a commit"
  return (seq, ops)

/-- What reading a record at a position finds. -/
inductive Next where
  | commit (seq : UInt64) (ops : Array Op) (next : Nat)
  /-- Nothing left, or a record that is cut short or fails its checksum: the log ends here. -/
  | end

/-- The record at `pos` of a log. -/
def nextRecord (log : ByteArray) (pos : Nat) : Next :=
  if pos + 12 > log.size then .end
  else
    let r : Reader := { data := log, pos }
    match
      (do
            let magic ← take 4
            let len ← u32
            let crc ← u32
            let payload ← take len
            return (magic, crc, payload) : P _).run
        r with
    | .error _ => .end
    | .ok ((magic, crc, payload), r') =>
      if magic != "NRCD".toUTF8 || (crc32 payload).toNat != crc then .end
      else
        match decodePayload payload with
        | .ok (seq, ops) => .commit seq ops r'.pos
        | .error _ => .end

end Near.Node.Store
