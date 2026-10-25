import NodeConformance.Runner
import NearNode.Primitives

/-!
The M1c part of the registry of `node-conformance-types` for state sync and the network types.
-/

open Near.Node Near.Node.Conformance Near.Node.Borsh

/-- The oracle records no value where nearcore overflows. -/
private def encodeOpt (x : Option UInt64) : ByteArray :=
  match x with
  | some n => Codec.encode n
  | none => ByteArray.empty

private def headerFields (h : ShardStateSyncResponseHeader) : List (String × ByteArray) :=
  [("numParts", encodeOpt h.numStateParts), ("heightIncluded", Codec.encode h.chunkHeightIncluded),
    ("prevStateRoot", h.chunkPrevStateRoot.bytes)]

/-- The decoded partial state of either version (a compressed part is a zstd frame). -/
private def partFields (p : StatePart) : List (String × ByteArray) :=
  [("payloadLength", Codec.encode p.payloadLength.toUInt64),
    ("partialState",
      match p.toPartialState? with
      | some s => Codec.encode s
      | none => ByteArray.empty)]

/-- Every state sync fixture type with its check. -/
def syncRegistry : List (String × Check) :=
  [("StateRootNode",
      check StateRootNode fun n => [("numParts", encodeOpt (getNumStateParts n.memoryUsage))]),
    ("ReceiptProofResponse", check ReceiptProofResponse), ("RootProof", check RootProof),
    ("StateHeaderKey", check StateHeaderKey), ("StatePartKey", check StatePartKey),
    ("PartIdOrHeader", check PartIdOrHeader), ("StateRequestAckBody", check StateRequestAckBody),
    ("StateRequestAck", check StateRequestAck),
    ("ShardStateSyncResponseHeaderV1", check ShardStateSyncResponseHeaderV1),
    ("ShardStateSyncResponseHeaderV2", check ShardStateSyncResponseHeaderV2),
    ("ShardStateSyncResponseHeader", check ShardStateSyncResponseHeader headerFields),
    ("BitArray", check BitArray), ("CachedParts", check CachedParts),
    ("StatePart", check StatePart partFields),
    ("ShardStateSyncResponseV1", check ShardStateSyncResponseV1),
    ("ShardStateSyncResponseV2", check ShardStateSyncResponseV2),
    ("ShardStateSyncResponseV3", check ShardStateSyncResponseV3),
    ("ShardStateSyncResponseV4", check ShardStateSyncResponseV4),
    ("ShardStateSyncResponse",
      check ShardStateSyncResponse fun r =>
        [("partId", Codec.encode r.partId), ("payloadLength", Codec.encode r.payloadLength)]),
    ("StateSyncDumpProgress", check StateSyncDumpProgress), ("PeerId", check PeerId),
    ("AnnounceAccount", check AnnounceAccount fun a => [("hash", a.hash.bytes)]),
    ("GenesisId", check GenesisId)]
