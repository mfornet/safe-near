import NearNode.Primitives.Basic

/-!
# Congestion info and bandwidth requests

`near-primitives::congestion_info` and `bandwidth_scheduler` at `=0.37.4`: the per-shard congestion
info and bandwidth requests carried by chunk headers, and the scheduler state kept in the trie.
-/

namespace Near.Node

open Borsh

/-- `CongestionInfoV1`. -/
structure CongestionInfoV1 where
  delayedReceiptsGas : U128
  bufferedReceiptsGas : U128
  receiptBytes : UInt64
  allowedShard : UInt16
  deriving BEq, Inhabited

instance : Codec CongestionInfoV1 :=
  .iso (U128 × U128 × UInt64 × UInt16) (fun (d, b, r, a) => ⟨d, b, r, a⟩) fun x =>
    (x.delayedReceiptsGas, x.bufferedReceiptsGas, x.receiptBytes, x.allowedShard)

/-- `CongestionInfo`: only V1 exists. -/
inductive CongestionInfo where
  | v1 (i : CongestionInfoV1)
  deriving BEq, Inhabited

instance : Codec CongestionInfo :=
  .enum "CongestionInfo"
    [.variant 0 CongestionInfoV1 .v1 fun
        | .v1 i => some i]

/-- `BandwidthRequestBitmap`: 40 bits in 5 bytes. -/
structure BandwidthRequestBitmap where
  data : ByteArray
  deriving BEq, Inhabited

instance : Codec BandwidthRequestBitmap :=
  .isoOf (.fixed 5) .mk BandwidthRequestBitmap.data

/-- `BandwidthRequest`. -/
structure BandwidthRequest where
  toShard : UInt16
  requestedValuesBitmap : BandwidthRequestBitmap
  deriving BEq, Inhabited

instance : Codec BandwidthRequest :=
  .iso (UInt16 × BandwidthRequestBitmap) (fun (s, b) => ⟨s, b⟩) fun x =>
    (x.toShard, x.requestedValuesBitmap)

/-- `BandwidthRequestsV1`. -/
structure BandwidthRequestsV1 where
  requests : Array BandwidthRequest
  deriving BEq, Inhabited

instance : Codec BandwidthRequestsV1 :=
  .iso (Array BandwidthRequest) .mk BandwidthRequestsV1.requests

/-- `BandwidthRequests`: only V1 exists. -/
inductive BandwidthRequests where
  | v1 (r : BandwidthRequestsV1)
  deriving BEq, Inhabited

instance : Codec BandwidthRequests :=
  .enum "BandwidthRequests"
    [.variant 0 BandwidthRequestsV1 .v1 fun
        | .v1 r => some r]

/-- `LinkAllowance`. -/
structure LinkAllowance where
  sender : ShardId
  receiver : ShardId
  allowance : UInt64
  deriving BEq, Inhabited

instance : Codec LinkAllowance :=
  .iso (ShardId × ShardId × UInt64) (fun (s, r, a) => ⟨s, r, a⟩) fun x =>
    (x.sender, x.receiver, x.allowance)

/-- `BandwidthSchedulerStateV1`. -/
structure BandwidthSchedulerStateV1 where
  linkAllowances : Array LinkAllowance
  sanityCheckHash : CryptoHash
  deriving BEq, Inhabited

instance : Codec BandwidthSchedulerStateV1 :=
  .iso (Array LinkAllowance × CryptoHash) (fun (l, h) => ⟨l, h⟩) fun x =>
    (x.linkAllowances, x.sanityCheckHash)

/-- `BandwidthSchedulerState`: only V1 exists. -/
inductive BandwidthSchedulerState where
  | v1 (s : BandwidthSchedulerStateV1)
  deriving BEq, Inhabited

instance : Codec BandwidthSchedulerState :=
  .enum "BandwidthSchedulerState"
    [.variant 0 BandwidthSchedulerStateV1 .v1 fun
        | .v1 s => some s]

/-- `BandwidthSchedulerParams`. -/
structure BandwidthSchedulerParams where
  baseBandwidth : UInt64
  maxShardBandwidth : UInt64
  maxSingleGrant : UInt64
  maxReceiptSize : UInt64
  maxAllowance : UInt64
  deriving BEq, Inhabited

instance : Codec BandwidthSchedulerParams :=
  .iso (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) (fun (b, s, g, r, a) => ⟨b, s, g, r, a⟩)
    fun x =>
    (x.baseBandwidth, x.maxShardBandwidth, x.maxSingleGrant, x.maxReceiptSize, x.maxAllowance)

end Near.Node
