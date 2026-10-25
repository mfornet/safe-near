import NearNode.Primitives
import NearNode.Trie.Witness
import NearNode.Validator.Messages
import NearNode.Zstd

/-!
# State witnesses

* **Compression.** `EncodedChunkStateWitness::encode` (`utils/compression.rs`) is the zstd stream of
  the Borsh `ChunkStateWitness`. `compressStored` writes a conforming zstd frame whose blocks are all
  raw (block type 0): no entropy coding, so the output is larger than `zstd`'s, but every decoder
  accepts it (frame header without content size, window descriptor 2^17, no checksum, blocks of at
  most 128 KiB, the last one flagged). The decoder in `NearNode.Zstd` and the `zstd` crate read it.
* **Parts.** `generate_state_witness_parts` (`partial_witness_actor.rs`) encodes the compressed bytes
  with a Reed-Solomon encoder for as many parts as there are chunk validators (60 % data parts); part
  `i` is the `PartialEncodedStateWitness` for validator `i`. With RS the payload is the Borsh of the
  `Box<[u8]>` (a length prefix and the bytes); a single part is the raw bytes
  (`serialize_single_part`).
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Borsh Near.Node.ReedSolomon

/-- A zstd frame of raw blocks. -/
def compressStored (data : ByteArray) : ByteArray :=
  Id.run do
    let maxBlock := 128 * 1024
    -- magic, frame header descriptor (no flags), window descriptor: exponent 7, mantissa 0
    let mut out := ByteArray.mk #[0x28, 0xb5, 0x2f, 0xfd, 0x00, 0x38]
    let n := data.size
    if n == 0 then
      return out.append (ByteArray.mk #[0x01, 0x00, 0x00])
    let mut pos := 0
    while pos < n do
      let len := min maxBlock (n - pos)
      let last : Nat := if pos + len == n then 1 else 0
      -- Block_Header: last flag, type 0 (raw), size in the upper 21 bits
      let header := last + len * 8
      out := out.push header.toUInt8
      out := out.push (header >>> 8).toUInt8
      out := out.push (header >>> 16).toUInt8
      out := out.append (data.extract pos (pos + len))
      pos := pos + len
    return out

/-- `EncodedChunkStateWitness::encode`. -/
def encodeWitness (w : ChunkStateWitness) : EncodedChunkStateWitness :=
  ⟨compressStored (Codec.encode w)⟩

/-- `ReedSolomonEncoder::encode` of an `EncodedChunkStateWitness`. -/
def encodeWitnessParts (e : Encoder) (w : EncodedChunkStateWitness) :
    Except String (Array ByteArray × Nat) :=
  match e.code with
  | some _ => e.encode (Codec.encode w)
  | none => pure (#[w.bytes], w.bytes.size)

/-- `generate_state_witness_parts`: for each chunk validator the part it owns, signed. -/
def witnessParts (s : Signer) (epochId : EpochId) (header : ShardChunkHeader)
    (w : EncodedChunkStateWitness) (validators : Array AccountId) :
    Except String (Array (AccountId × PartialEncodedStateWitness)) := do
  let enc ← Encoder.new validators.size witnessRatio
  let encoded ← encodeWitnessParts enc w
  let parts := encoded.1
  let encodedLength := encoded.2
  if parts.size != validators.size then
    throw "the parts and the validators differ in number"
  pure <|
      (validators.zip parts).zipIdx.map fun ((v, part), i) =>
        (v, newPartialWitness s epochId header i part encodedLength)

end Near.Node.Validator
