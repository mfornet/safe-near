import NearNode.Primitives.Map

/-!
# Shard layouts

`near-primitives::shard_layout` at `=0.37.4`: the four layout versions, `ShardUId`, and the pure
lookups between shard ids, shard indexes and accounts. Layouts derive their parent and ancestor
maps when they are built; Borsh stores them without checking, so decoding does not either.
Lookups return `none` where nearcore returns an error or panics.
-/

namespace Near.Node

open Borsh

/-- `ShardUId`: a shard id under a layout version. -/
structure ShardUId where
  version : UInt32
  shardId : UInt32
  deriving BEq, Inhabited

instance : Codec ShardUId :=
  .iso (UInt32 × UInt32) (fun (v, s) => ⟨v, s⟩) fun x => (x.version, x.shardId)

/-- `ShardLayoutV0`: accounts are spread by hash over `numShards` shards. -/
structure ShardLayoutV0 where
  numShards : UInt64
  version : UInt32
  deriving BEq, Inhabited

instance : Codec ShardLayoutV0 :=
  .iso (UInt64 × UInt32) (fun (n, v) => ⟨n, v⟩) fun x => (x.numShards, x.version)

/-- `ShardLayoutV1`: account ranges, with shard ids that are also the indexes. -/
structure ShardLayoutV1 where
  boundaryAccounts : Array AccountId
  shardsSplitMap : Option (Array (Array ShardId))
  toParentShardMap : Option (Array ShardId)
  version : UInt32
  deriving BEq, Inhabited

instance : Codec ShardLayoutV1 :=
  .iso (Array AccountId × Option (Array (Array ShardId)) × Option (Array ShardId) × UInt32)
    (fun (b, s, p, v) => ⟨b, s, p, v⟩) fun x =>
    (x.boundaryAccounts, x.shardsSplitMap, x.toParentShardMap, x.version)

/-- `ShardLayoutV2`. -/
structure ShardLayoutV2 where
  boundaryAccounts : Array AccountId
  shardIds : Array ShardId
  idToIndexMap : SortedMap ShardId UInt64
  indexToIdMap : SortedMap UInt64 ShardId
  shardsSplitMap : Option (SortedMap ShardId (Array ShardId))
  shardsParentMap : Option (SortedMap ShardId ShardId)
  version : UInt32
  deriving BEq, Inhabited

instance : Codec ShardLayoutV2 :=
  .iso
    (Array AccountId ×
      Array ShardId ×
      SortedMap ShardId UInt64 ×
      SortedMap UInt64 ShardId ×
      Option (SortedMap ShardId (Array ShardId)) × Option (SortedMap ShardId ShardId) × UInt32)
    (fun (b, i, m, n, s, p, v) => ⟨b, i, m, n, s, p, v⟩) fun x =>
    (x.boundaryAccounts, x.shardIds, x.idToIndexMap, x.indexToIdMap, x.shardsSplitMap,
      x.shardsParentMap, x.version)

/-- `ShardLayoutV3`. -/
structure ShardLayoutV3 where
  boundaryAccounts : Array AccountId
  shardIds : Array ShardId
  idToIndexMap : SortedMap ShardId UInt64
  shardsSplitMap : SortedMap ShardId (Array ShardId)
  lastSplit : ShardId
  shardsAncestorMap : SortedMap ShardId (Array ShardId)
  deriving BEq, Inhabited

instance : Codec ShardLayoutV3 :=
  .iso
    (Array AccountId ×
      Array ShardId ×
      SortedMap ShardId UInt64 ×
      SortedMap ShardId (Array ShardId) × ShardId × SortedMap ShardId (Array ShardId))
    (fun (b, i, m, s, l, a) => ⟨b, i, m, s, l, a⟩) fun x =>
    (x.boundaryAccounts, x.shardIds, x.idToIndexMap, x.shardsSplitMap, x.lastSplit,
      x.shardsAncestorMap)

/-- `ShardLayout`. -/
inductive ShardLayout where
  | v0 (l : ShardLayoutV0)
  | v1 (l : ShardLayoutV1)
  | v2 (l : ShardLayoutV2)
  | v3 (l : ShardLayoutV3)
  deriving BEq, Inhabited

instance : Codec ShardLayout :=
  .enum "ShardLayout"
    [.variant 0 ShardLayoutV0 .v0 fun
        | .v0 l => some l
        | _ => none,
      .variant 1 ShardLayoutV1 .v1 fun
        | .v1 l => some l
        | _ => none,
      .variant 2 ShardLayoutV2 .v2 fun
        | .v2 l => some l
        | _ => none,
      .variant 3 ShardLayoutV3 .v3 fun
        | .v3 l => some l
        | _ => none]

namespace ShardLayout

/-- `ShardLayout::version`. -/
def version : ShardLayout → UInt32
  | .v0 l => l.version
  | .v1 l => l.version
  | .v2 l => l.version
  | .v3 _ => 3

/-- `ShardLayout::num_shards`. -/
def numShards : ShardLayout → UInt64
  | .v0 l => l.numShards
  | .v1 l => (l.boundaryAccounts.size + 1).toUInt64
  | .v2 l => l.shardIds.size.toUInt64
  | .v3 l => l.shardIds.size.toUInt64

/-- `ShardLayout::shard_ids`. -/
def shardIds : ShardLayout → Array ShardId
  | .v0 l => (Array.range l.numShards.toNat).map Nat.toUInt64
  | .v1 l => (Array.range (l.boundaryAccounts.size + 1)).map Nat.toUInt64
  | .v2 l => l.shardIds
  | .v3 l => l.shardIds

/-- `ShardLayout::get_shard_index`. In V0 and V1 the shard id is the index. -/
def getShardIndex : ShardLayout → ShardId → Option Nat
  | .v0 _, s => some s.toNat
  | .v1 _, s => some s.toNat
  | .v2 l, s => (l.idToIndexMap.find? s).map (·.toNat)
  | .v3 l, s => (l.idToIndexMap.find? s).map (·.toNat)

/-- `ShardLayout::get_shard_id`. -/
def getShardId : ShardLayout → Nat → Option ShardId
  | .v0 l, i => if i < l.numShards.toNat then some i.toUInt64 else none
  | .v1 l, i => if i < l.boundaryAccounts.size + 1 then some i.toUInt64 else none
  | .v2 l, i => l.shardIds[i]?
  | .v3 l, i => l.shardIds[i]?

/-- Whether `boundaries` are in ascending order, as every constructed layout asserts. -/
private def sorted (boundaries : Array AccountId) : Bool :=
  (boundaries.zip (boundaries.extract 1 boundaries.size)).all fun (a, b) => compare a b != .gt

/-- The number of leading boundaries `<= a`: `V1` stops at the first boundary above `a`. -/
private def leading (a : AccountId) : List AccountId → Nat
  | [] => 0
  | b :: bs => if compare a b == .lt then 0 else leading a bs + 1

/-- The index of the first boundary above `a` (`partition_point(|x| x <= a)`) in sorted
boundaries. -/
private def partitionPoint (boundaries : Array AccountId) (a : AccountId) : Nat :=
  boundaries.foldl (init := 0) fun n b => if compare b a != .gt then n + 1 else n

/-- `ShardLayout::account_id_to_shard_id`. The search of `V2` and `V3` is only defined for sorted
boundaries (every constructor asserts it), so other layouts give `none`. -/
def accountIdToShardId : ShardLayout → AccountId → Option ShardId
  | .v0 l, a =>
    if l.numShards == 0 then none
    else
      let h := (CryptoHash.hash a.val.toUTF8).bytes
      let v := (List.range 8).foldr (fun i acc => acc * 256 + h[i]!.toNat) 0
      some (UInt64.ofNat (v % l.numShards.toNat))
  | .v1 l, a => some (leading a l.boundaryAccounts.toList).toUInt64
  | .v2 l, a =>
    if sorted l.boundaryAccounts then l.shardIds[partitionPoint l.boundaryAccounts a]? else none
  | .v3 l, a =>
    if sorted l.boundaryAccounts then l.shardIds[partitionPoint l.boundaryAccounts a]? else none

end ShardLayout

end Near.Node
