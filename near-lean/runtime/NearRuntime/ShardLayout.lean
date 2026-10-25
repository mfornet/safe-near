import NearRuntime.Wire

/-! # Shard layout

`ShardLayout::V2` of `core/primitives/src/shard_layout/v2.rs`: the boundary accounts split the
account space into ranges, and the shard at index `i` serves `[boundaries[i - 1], boundaries[i])`.
Shard ids need not be sorted or contiguous: iteration order is the order of `shardIds`, which fixes
the order in which buffers are forwarded, bandwidth requests are listed and the allowed shard is
chosen, so it is kept as given.

nearcore divergence: layouts V0, V1 and V3 and layouts with a split history (`shards_split_map`,
resharding) are not represented; `ShardLayout.ofBorsh` rejects them. -/
namespace Near.Sharding

structure ShardLayout where
  boundaries : List AccountId
  shardIds : List Nat
  deriving Repr, BEq, Inhabited

namespace ShardLayout

/-- The single-shard layout of the reference configuration. -/
def single : ShardLayout := { boundaries := [], shardIds := [0] }

def numShards (layout : ShardLayout) : Nat := layout.shardIds.length

/-- `get_shard_index`. -/
def index? (layout : ShardLayout) (shard : Nat) : Option Nat :=
  layout.shardIds.findIdx? (· == shard) |>.filter (· < layout.shardIds.length)

/-- `get_shard_id`. -/
def id? (layout : ShardLayout) (index : Nat) : Option Nat := layout.shardIds[index]?

/-- `boundary_accounts.partition_point(|x| x <= account_id)` of `account_id_to_shard_id`. -/
def accountIndex (layout : ShardLayout) (account : AccountId) : Nat :=
  (layout.boundaries.takeWhile fun boundary => !decide (account < boundary)).length

/-- `account_id_to_shard_id`. -/
def accountShard (layout : ShardLayout) (account : AccountId) : Nat :=
  layout.shardIds.getD (layout.accountIndex account) 0

/-- Whether the layout has this shard. -/
def contains (layout : ShardLayout) (shard : Nat) : Bool := layout.shardIds.contains shard

private def pairs : Wire.Parser (Nat × Nat) := do
  let first ← Wire.uint 8
  return (first, ← Wire.uint 8)

/-- Borsh `ShardLayout`, V2 only. The two index maps are checked against the shard id list. -/
def ofBorsh : Bytes → Except String ShardLayout := Wire.run do
  unless (← Wire.uint 1) == 2 do throw "unsupported shard layout version (only V2)"
  let boundaries ← Wire.repeatN (← Wire.uint 4) Wire.string
  let shardIds ← Wire.repeatN (← Wire.uint 4) (Wire.uint 8)
  let idToIndex ← Wire.repeatN (← Wire.uint 4) pairs
  let indexToId ← Wire.repeatN (← Wire.uint 4) pairs
  let splitMap ← Wire.uint 1
  let parentMap ← Wire.uint 1
  let _version ← Wire.uint 4
  unless splitMap == 0 && parentMap == 0 do throw "shard layouts with a split history are unsupported"
  unless boundaries.length + 1 == shardIds.length do throw "boundary and shard counts disagree"
  unless boundaries.zip (boundaries.drop 1) |>.all (fun (a, b) => decide (a < b)) do
    throw "boundary accounts are not sorted"
  unless shardIds.eraseDups.length == shardIds.length do throw "duplicate shard id"
  let indexed := shardIds.zipIdx
  unless indexToId == indexed.map (fun (id, i) => (i, id)) do throw "index_to_id_map disagrees"
  unless idToIndex == (indexed.map fun (id, i) => (id, i)).mergeSort (fun a b => a.1 ≤ b.1) do
    throw "id_to_index_map disagrees"
  return { boundaries, shardIds }

end ShardLayout

end Near.Sharding
