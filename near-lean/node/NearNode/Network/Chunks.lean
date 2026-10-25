import NearNode.Network.Types
import NearNode.Chain.Apply

/-!
# Chunk bodies from a peer

A block carries chunk headers; the transactions of a chunk are in its body, which a peer holds as the
parts of a Reed-Solomon code (`chain/chunks/src`, `core/primitives/src/{sharding,reed_solomon}.rs`).
The first `num_data_parts` parts, concatenated and cut at the `encoded_length` of the header, are the
Borsh `TransactionReceipt` of the chunk (its transactions and the outgoing receipts of the previous
chunk), so a body is rebuilt from the data parts alone when the peer has all of them, which a peer
that tracks the shard does. A part is accepted when its merkle path leads to the header's
`encoded_merkle_root`.

The request is a routed `PartialEncodedChunkRequest` to the peer, answered by a routed
`PartialEncodedChunkResponse` addressed to the hash of the request.
-/

namespace Near.Node.Network

open Near.Node Near.Node.Borsh

/-- `EpochManager::num_total_parts`: the block producer seats of the genesis configuration, at least
two. -/
def numTotalParts (blockProducerSeats : Nat) : Nat :=
  if blockProducerSeats > 1 then blockProducerSeats else 2

/-- `num_data_parts`. -/
def numDataParts (total : Nat) : Nat :=
  if total ≤ 3 then 1 else (total - 1) / 3

/-- The length of the encoded chunk. -/
def _root_.Near.Node.ShardChunkHeaderInner.encodedLength : ShardChunkHeaderInner → UInt64
  | .v1 i => i.encodedLength
  | .v2 i => i.encodedLength
  | .v3 i => i.encodedLength
  | .v4 i => i.encodedLength
  | .v5 i => i.encodedLength
  | .v6 i => i.encodedLength

/-- The length of the encoded chunk of a header. -/
def _root_.Near.Node.ShardChunkHeader.encodedLength : ShardChunkHeader → UInt64
  | .v1 h => h.inner.encodedLength
  | .v2 h => h.inner.encodedLength
  | .v3 h => h.inner.encodedLength

/-- `PartialEncodedChunkRequestMsg` for every part of the chunk. -/
def chunkRequest (h : ShardChunkHeader) (total : Nat) : PartialEncodedChunkRequestMsg :=
  { chunkHash := h.chunkHash.hash, partOrds := (Array.range total).map (·.toUInt64),
    trackingShards := ⟨#[]⟩ }

/-- The parts of one chunk received so far. -/
structure ChunkParts where
  header : ShardChunkHeader
  parts : Std.HashMap UInt64 ByteArray := {}

/-- Adds the parts of a response that belong to the chunk and whose merkle path is valid. Returns
how many were refused. -/
def ChunkParts.add (c : ChunkParts) (total : Nat) (r : PartialEncodedChunkResponseMsg) :
    ChunkParts × Nat :=
  Id.run do
    let mut c := c
    let mut refused := 0
    if r.chunkHash != c.header.chunkHash.hash then
      return (c, r.parts.size)
    for p in r.parts do
      if p.partOrd.toNat < total && verifyPath c.header.encodedMerkleRoot p.merkleProof p.part then
        c := { c with parts := c.parts.insert p.partOrd p.part }
      else
        refused := refused + 1
    return (c, refused)

/-- Whether all data parts are there. -/
def ChunkParts.complete (c : ChunkParts) (dataParts : Nat) : Bool :=
  (List.range dataParts).all fun i => c.parts.contains i.toUInt64

/-- The body of the chunk: the data parts concatenated, cut at the encoded length, decoded. -/
def ChunkParts.body (c : ChunkParts) (dataParts : Nat) : Except String TransactionReceipt := do
  let mut raw := ByteArray.empty
  for i in [0:dataParts] do
    match c.parts[i.toUInt64]? with
    | some p =>
      raw := raw ++ p
    | none =>
      throw s!"data part {i} is missing"
  let n := c.header.encodedLength.toNat
  if raw.size < n then
    throw "the parts are shorter than the encoded length"
  match Codec.decodeAll (α := TransactionReceipt) (raw.extract 0 n) with
  | .ok b =>
    pure b
  | .error e =>
    throw s!"the chunk body does not decode: {repr e}"

end Near.Node.Network
