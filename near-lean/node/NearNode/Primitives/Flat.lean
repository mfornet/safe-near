import NearNode.Primitives.TrieNode
import NearNode.Primitives.ShardLayout

/-!
# Flat storage types

`core/store/src/flat/{types,delta}.rs` (nearcore `44f7ae6`): the block a flat head is, the metadata
and changes of a block's delta, and the status of a shard's flat storage. The status has the
variants `Disabled`, `Empty` and `Ready`; `Creation` (deprecated) and `Resharding` are rejected
until resharding is built.
-/

namespace Near.Node

open Borsh

/-- `flat::BlockInfo`. -/
structure FlatBlockInfo where
  hash : CryptoHash
  height : BlockHeight
  prevHash : CryptoHash
  deriving BEq, Inhabited

instance : Codec FlatBlockInfo :=
  .iso (CryptoHash × BlockHeight × CryptoHash) (fun (h, n, p) => ⟨h, n, p⟩) fun x =>
    (x.hash, x.height, x.prevHash)

/-- `BlockWithChangesInfo`. -/
structure BlockWithChangesInfo where
  hash : CryptoHash
  height : BlockHeight
  deriving BEq, Inhabited

instance : Codec BlockWithChangesInfo :=
  .iso (CryptoHash × BlockHeight) (fun (h, n) => ⟨h, n⟩) fun x => (x.hash, x.height)

/-- `FlatStateDeltaMetadata`: the block, and for a block without changes the closest earlier block
with some. -/
structure FlatStateDeltaMetadata where
  block : FlatBlockInfo
  prevBlockWithChanges : Option BlockWithChangesInfo
  deriving BEq, Inhabited

instance : Codec FlatStateDeltaMetadata :=
  .iso (FlatBlockInfo × Option BlockWithChangesInfo) (fun (b, p) => ⟨b, p⟩) fun x =>
    (x.block, x.prevBlockWithChanges)

/-- `FlatStateChanges`: a `HashMap`, serialized in key order. A `none` value deletes the key. -/
abbrev FlatStateChanges :=
  Array (ByteArray × Option FlatStateValue)

instance : Codec FlatStateChanges :=
  .btreeMap compareBytes inferInstance inferInstance

/-- `KeyForFlatStateDelta::to_bytes` and the prefix of a `FlatState` key: the `ShardUId` as 8 bytes. -/
def ShardUId.key (u : ShardUId) : ByteArray :=
  Codec.encode u

/-- `FlatStorageReadyStatus`. -/
inductive FlatStorageStatus where
  | disabled
  | empty
  | ready (flatHead : FlatBlockInfo)
  deriving BEq, Inhabited

instance : Codec FlatStorageStatus :=
  .enum "FlatStorageStatus"
    [.const 0 .disabled, .const 1 .empty,
      .variant 3 FlatBlockInfo .ready fun
        | .ready h => some h
        | _ => none]

end Near.Node
