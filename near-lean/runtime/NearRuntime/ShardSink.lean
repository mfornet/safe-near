import NearRuntime.Congestion
import NearRuntime.Bandwidth

/-! # Outgoing receipts: forwarding, buffers and bandwidth requests

`runtime/runtime/src/congestion_control.rs` (`ReceiptSinkV2`), `core/store/src/trie/outgoing_metadata.rs`
and `receipts_column_helper.rs`: a receipt for another shard is sent at once if the receiver's gas
limit (congestion control) and the granted bandwidth (scheduler) allow, and is otherwise appended to
the outgoing buffer for that shard, which is part of the shard's trie. At the start of the next chunk
buffered receipts are forwarded first, in order, until the first one that does not fit.

Buffered receipts are opaque Borsh bytes with their stored metadata (`StateStoredReceipt`): they are
only moved, never executed, so nothing about their actions is needed here.

nearcore divergence: layouts with a split history (receipts buffered for a parent shard) are not
represented, and an own congestion info that is absent from the chunk's input is an error where
nearcore would bootstrap it by scanning the delayed and buffered receipts. -/
namespace Near.ShardSink

open Near.Sharding Near.Congestion Near.Bandwidth

/-! ## What is stored -/

/-- `StateStoredReceipt`: a Borsh receipt with the gas and size it was stored with. Version 1
(`V1`) buffers also feed the group metadata, version 0 do not. -/
structure Stored where
  receipt : Bytes
  version : Nat
  gas : Nat
  size : Nat
  deriving BEq, Repr, Inhabited

def Stored.toBorsh (stored : Stored) : Bytes :=
  [255, 255, UInt8.ofNat stored.version] ++ stored.receipt ++ Wire.little 8 stored.gas ++
    Wire.little 8 stored.size

def Stored.ofBorsh (bytes : Bytes) : Except String Stored := do
  unless bytes.length ≥ 3 + 16 && bytes.take 2 == [255, 255] do
    throw "stored receipt without the state-stored tag"
  let version := bytes[2]!.toNat
  unless version ≤ 1 do throw "unknown state-stored receipt version"
  let body := bytes.drop 3
  let cut := body.length - 16
  return { receipt := body.take cut, version, gas := Wire.number ((body.drop cut).take 8)
           size := Wire.number (body.drop (cut + 8)) }

/-- The part of a Borsh receipt that decides its shard (`Receipt::receiver_shard_id`). -/
structure Route where
  receiver : AccountId
  /-- `GlobalContractDistribution` goes to its target shard instead of the receiver's. -/
  target : Option Nat

/-- Read the receiver (and a distribution's target shard) from a Borsh `Receipt`. -/
def Route.ofReceipt : Bytes → Except String Route := Wire.runPrefix do
  let _predecessor ← Wire.string
  let receiver ← Wire.string
  let _id ← Wire.take 32
  let tag ← Wire.uint 1
  if tag == 4 then
    let _version ← Wire.uint 1
    let kind ← Wire.uint 1
    let _identifier ← if kind == 0 then Wire.take 32 else Wire.take (← Wire.uint 4)
    return { receiver, target := some (← Wire.uint 8) }
  else return { receiver, target := none }

/-- `receiver_shard_id`. -/
def Route.shard (route : Route) (layout : ShardLayout) : Nat :=
  match route.target with
  | some target => target
  | none => layout.accountShard route.receiver

/-- One outgoing buffer: the index of its first item and the items. -/
structure Queue where
  first : Nat
  items : List Stored
  deriving BEq, Repr, Inhabited

/-- A group of consecutive buffered receipts (`ReceiptGroupV0`). -/
structure Group where
  size : Nat
  gas : Nat
  deriving BEq, Repr, Inhabited

/-- `ReceiptGroupsQueue`: groups, with the totals over all receipts of the buffer. -/
structure Groups where
  first : Nat := 0
  groups : List Group := []
  totalSize : Nat := 0
  totalGas : Nat := 0
  totalReceipts : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Everything a shard keeps about its outgoing buffers, ordered by receiving shard id. -/
structure Buffers where
  queues : List (Nat × Queue) := []
  groups : List (Nat × Groups) := []
  deriving BEq, Repr, Inhabited

private def upsert (key : Nat) (value : α) : List (Nat × α) → List (Nat × α)
  | [] => [(key, value)]
  | (k, v) :: rest =>
    if k == key then (k, value) :: rest
    else if key < k then (key, value) :: (k, v) :: rest
    else (k, v) :: upsert key value rest

namespace Buffers

def queue? (b : Buffers) (shard : Nat) : Option Queue := (b.queues.find? (·.1 == shard)).map (·.2)

def length (b : Buffers) (shard : Nat) : Nat := ((b.queue? shard).map (·.items.length)).getD 0

/-- `push_back` (creating the buffer's indices on first use). -/
def pushBack (b : Buffers) (shard : Nat) (item : Stored) : Buffers :=
  let q := (b.queue? shard).getD { first := 0, items := [] }
  { b with queues := upsert shard { q with items := q.items ++ [item] } b.queues }

/-- `pop_n`: drop the first `n` items; an empty buffer stays in the indices. -/
def popN (b : Buffers) (shard n : Nat) : Buffers :=
  match b.queue? shard with
  | none => b
  | some q =>
    let n := min n q.items.length
    if n == 0 then b
    else { b with queues := upsert shard { first := q.first + n, items := q.items.drop n } b.queues }

/-- `ReceiptGroupsConfig::default_config`: groups of at most 100 kB (`ByteSize::kb`) and no gas bound. -/
def groupSizeBound : Nat := 100_000

/-- `update_on_receipt_pushed`. -/
def groupPushed (b : Buffers) (shard size gas : Nat) : Except String Buffers := do
  let g := (b.groups.find? (·.1 == shard)).map (·.2) |>.getD {}
  let totalSize := g.totalSize + size
  let totalGas := g.totalGas + gas
  unless totalSize < 2 ^ 64 && totalGas < 2 ^ 128 do throw "receipt group totals overflow"
  let groups := match g.groups.getLast? with
    | none => [({ size, gas } : Group)]
    | some last =>
      if last.size + size > groupSizeBound || last.gas + gas > 2 ^ 64 - 1 then
        g.groups ++ [{ size, gas }]
      else g.groups.dropLast ++ [{ size := last.size + size, gas := last.gas + gas }]
  let updated : Groups := { g with groups, totalSize, totalGas, totalReceipts := g.totalReceipts + 1 }
  return { b with groups := upsert shard updated b.groups }

/-- `update_on_receipt_popped`. -/
def groupPopped (b : Buffers) (shard size gas : Nat) : Except String Buffers := do
  let some g := (b.groups.find? (·.1 == shard)).map (·.2)
    | throw "no receipt group metadata for the shard"
  unless size ≤ g.totalSize && gas ≤ g.totalGas && g.totalReceipts ≥ 1 do
    throw "receipt group totals underflow"
  let some head := g.groups.head? | throw "no receipt groups to pop from"
  unless size ≤ head.size && gas ≤ head.gas do throw "receipt group underflow"
  let head : Group := { size := head.size - size, gas := head.gas - gas }
  unless head.size != 0 || head.gas == 0 do throw "an empty receipt group still has gas"
  let (first, groups) :=
    if head.size == 0 then (g.first + 1, g.groups.drop 1) else (g.first, head :: g.groups.drop 1)
  let updated : Groups := { first, groups, totalSize := g.totalSize - size
                            totalGas := g.totalGas - gas, totalReceipts := g.totalReceipts - 1 }
  return { b with groups := upsert shard updated b.groups }

/-- The trie columns of the buffers: `BufferedReceiptIndices` (13), `BufferedReceipt` (14),
`BufferedReceiptGroupsQueueData` (16) and `BufferedReceiptGroupsQueueItem` (17). -/
def entries (b : Buffers) : Except String (List (Bytes × Bytes)) := do
  let indices :=
    if b.queues.isEmpty then []
    else [([13], Wire.little 4 b.queues.length ++ (b.queues.map fun (shard, q) =>
      Wire.little 8 shard ++ Wire.little 8 q.first ++ Wire.little 8 (q.first + q.items.length)).flatten)]
  let mut items := []
  for (shard, q) in b.queues do
    unless shard < 2 ^ 16 do throw "buffered receipt shard id exceeds u16"
    for (item, offset) in q.items.zipIdx do
      items := items ++ [([14] ++ Wire.little 2 shard ++ Wire.little 8 (q.first + offset), item.toBorsh)]
  let mut metadata := []
  for (shard, g) in b.groups do
    metadata := metadata ++ [([16] ++ Wire.little 8 shard,
      [0] ++ Wire.little 8 g.first ++ Wire.little 8 (g.first + g.groups.length) ++
        Wire.little 8 g.totalSize ++ Wire.little 16 g.totalGas ++ Wire.little 8 g.totalReceipts)]
    for (group, offset) in g.groups.zipIdx do
      metadata := metadata ++ [([17] ++ Wire.little 8 shard ++ Wire.little 8 (g.first + offset),
        [0] ++ Wire.little 8 group.size ++ Wire.little 16 group.gas)]
  return indices ++ items ++ metadata

/-- Rebuild the buffers from their raw trie entries (columns 13, 14, 16 and 17). Every entry must be
consumed; `entries` of the result reproduces them. -/
def ofEntries (raw : List (Bytes × Bytes)) : Except String Buffers := do
  let find (key : Bytes) : Option Bytes := (raw.find? (·.1 == key)).map (·.2)
  let mut queues : List (Nat × Queue) := []
  match find [13] with
  | none => pure ()
  | some value =>
    let shards ← (Wire.run do
      Wire.repeatN (← Wire.uint 4) do
        let shard ← Wire.uint 8
        let first ← Wire.uint 8
        return (shard, first, ← Wire.uint 8)) value
    for (shard, first, next) in shards do
      let mut items := []
      for index in List.range (next - first) do
        let some bytes := find ([14] ++ Wire.little 2 shard ++ Wire.little 8 (first + index))
          | throw "buffered receipt referenced by the indices is missing"
        items := items ++ [← Stored.ofBorsh bytes]
      queues := queues ++ [(shard, { first, items })]
  let mut groups : List (Nat × Groups) := []
  for (shard, _) in queues do
    let some value := find ([16] ++ Wire.little 8 shard) | continue
    let (first, next, totalSize, totalGas, totalReceipts) ← (Wire.run do
      unless (← Wire.uint 1) == 0 do throw "unknown receipt groups version"
      let first ← Wire.uint 8
      let next ← Wire.uint 8
      let totalSize ← Wire.uint 8
      let totalGas ← Wire.uint 16
      return (first, next, totalSize, totalGas, ← Wire.uint 8)) value
    let mut list := []
    for index in List.range (next - first) do
      let some bytes := find ([17] ++ Wire.little 8 shard ++ Wire.little 8 (first + index))
        | throw "receipt group referenced by the indices is missing"
      let group ← (Wire.run do
        unless (← Wire.uint 1) == 0 do throw "unknown receipt group version"
        let size ← Wire.uint 8
        return ({ size, gas := ← Wire.uint 16 } : Group)) bytes
      list := list ++ [group]
    groups := groups ++ [(shard, { first, groups := list, totalSize, totalGas, totalReceipts })]
  let built : Buffers := { queues, groups }
  let rebuilt ← built.entries
  unless rebuilt.length == raw.length && raw.all (fun entry => rebuilt.contains entry) do
    throw "buffer columns are not canonical (stray, reordered or unrepresented entries)"
  return built

end Buffers

/-! ## The sink -/

/-- `OutgoingLimit`. -/
structure Limit where
  gas : Nat
  size : Nat
  deriving Repr

/-- `Gas::MAX`. -/
def gasMax : Nat := 2 ^ 64 - 1

/-- `ReceiptSinkV2`. -/
structure Sink where
  config : Config
  layout : ShardLayout
  shard : Nat
  info : Info
  /-- Receipts sent out this chunk (Borsh), in order. -/
  outgoing : List Bytes := []
  limits : List (Nat × Limit)
  buffers : Buffers

/-- A shard's congestion as the chunk's input lists it. -/
structure ShardCongestion where
  info : Info
  missedChunks : Nat

namespace Sink

/-- `ReceiptSink::new`: limits of every shard that has congestion info, from the congestion gas
limit of the receiver and the bandwidth granted from this shard to it. -/
def create (config : Config) (layout : ShardLayout) (shard : Nat) (own : Info)
    (congestion : List (Nat × ShardCongestion)) (output : Output) (buffers : Buffers) : Sink :=
  let limits := congestion.map fun (other, c) =>
    let gas := if other != shard then
        ({ config, info := c.info, missedChunks := c.missedChunks : Control }).outgoingGasLimit shard
      else gasMax
    let size := match layout.index? shard, layout.index? other with
      | some s, some r => output.grant s r
      | _, _ => 0
    (other, { gas, size : Limit })
  { config, layout, shard, info := own, limits, buffers }

/-- `try_forward`: send the receipt if both limits allow it, charging them; a size above
`max_receipt_size` counts as `max_receipt_size`. Shards without a limit get none (`Gas::MAX`, 0 bytes). -/
def tryForward (s : Sink) (receipt : Bytes) (gas size target : Nat) : Option Sink :=
  let size' := min size s.config.maxReceiptSize
  let limit := (s.limits.find? (·.1 == target)).map (·.2) |>.getD { gas := gasMax, size := 0 }
  let admission := if s.config.clampOutgoingGasAdmission then min gas s.config.allowedShardOutgoingGas else gas
  if limit.gas ≥ admission && limit.size ≥ size' then
    let limit := { gas := limit.gas - min limit.gas gas, size := limit.size - size' }
    some { s with outgoing := s.outgoing ++ [receipt]
                  limits := (target, limit) :: s.limits.filter (·.1 != target) }
  else none

/-- `forward_from_buffer_to_shard`. -/
def forwardFromBuffer (s : Sink) (bufferShard : Nat) : Except String Sink := do
  let some queue := s.buffers.queue? bufferShard | return s
  let mut s := s
  let mut forwarded := 0
  let mut popped : List (Nat × Nat) := []
  for item in queue.items do
    let route ← Route.ofReceipt item.receipt
    match s.tryForward item.receipt item.gas item.size (route.shard s.layout) with
    | none => break
    | some next =>
      s := { next with info := ← (← next.info.removeReceiptBytes item.size).removeBufferedGas item.gas }
      if item.version == 1 then popped := popped ++ [(item.size, item.gas)]
      forwarded := forwarded + 1
  s := { s with buffers := s.buffers.popN bufferShard forwarded }
  for (size, gas) in popped do
    s := { s with buffers := ← s.buffers.groupPopped bufferShard size gas }
  return s

/-- `forward_from_buffer`: every buffer, in the layout's shard order. -/
def forwardAll (s : Sink) : Except String Sink :=
  s.layout.shardIds.foldlM (fun s shard => s.forwardFromBuffer shard) s

/-- `forward_or_buffer_receipt`, with the receipt's congestion gas computed by the caller. -/
def forwardOrBuffer (s : Sink) (receipt : Bytes) (gas : Nat) : Except String Sink := do
  let target := (← Route.ofReceipt receipt).shard s.layout
  let size := receipt.length
  match s.tryForward receipt gas size target with
  | some next => return next
  | none =>
    let info ← (← s.info.addReceiptBytes size).addBufferedGas gas
    let buffers := s.buffers.pushBack target { receipt, version := 1, gas, size }
    return { s with info, buffers := ← buffers.groupPushed target size gas }

/-- `generate_bandwidth_requests`: one request per shard, in layout order, from the sizes of the
receipt groups in its buffer (or `max_receipt_size` when the group metadata is incomplete). -/
def requests (s : Sink) (params : Params) : List Request :=
  s.layout.shardIds.filterMap fun shard =>
    let length := s.buffers.length shard
    let sizes :=
      if length == 0 then []
      else match (s.buffers.groups.find? (·.1 == shard)).map (·.2) with
        | some g => if g.totalReceipts == length then g.groups.map (·.size) else [params.maxReceiptSize]
        | none => [params.maxReceiptSize]
    makeRequest shard (sizes.map (min · params.maxReceiptSize)) params

end Sink

end Near.ShardSink
