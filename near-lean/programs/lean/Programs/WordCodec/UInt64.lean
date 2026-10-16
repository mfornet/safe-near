import Programs.WordCodec
import Programs.ByteReassembly

/-!
# The eight-byte little-endian `u64` codec

Copied from the stream layer of Talos `codelib/CodeLib/Examples/SelectionSort/StdIO.lean`,
where it is `Wasm.Examples.SelectionSort.StdIO.codec`.
-/

namespace Wasm.WordCodec.U64

/-- The eight little-endian bytes of an unsigned 64-bit word. -/
def encodeWord (value : UInt64) : List UInt8 :=
  [ (value &&& 0xff).toUInt8
  , ((value >>> 8) &&& 0xff).toUInt8
  , ((value >>> 16) &&& 0xff).toUInt8
  , ((value >>> 24) &&& 0xff).toUInt8
  , ((value >>> 32) &&& 0xff).toUInt8
  , ((value >>> 40) &&& 0xff).toUInt8
  , ((value >>> 48) &&& 0xff).toUInt8
  , ((value >>> 56) &&& 0xff).toUInt8 ]

/-- Reassemble an unsigned 64-bit word from its little-endian bytes. -/
def decodeWord (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : UInt8) : UInt64 :=
  b₀.toUInt64 ||| (b₁.toUInt64 <<< 8) |||
    (b₂.toUInt64 <<< 16) ||| (b₃.toUInt64 <<< 24) |||
    (b₄.toUInt64 <<< 32) ||| (b₅.toUInt64 <<< 40) |||
    (b₆.toUInt64 <<< 48) ||| (b₇.toUInt64 <<< 56)

/-- `decodeWord` on the eight-byte chunks `WordCodec.deserialize` hands it. The
fallback case is unreachable: chunks are always exactly `width` bytes long. -/
def decodeChunk : List UInt8 → UInt64
  | b₀ :: b₁ :: b₂ :: b₃ :: b₄ :: b₅ :: b₆ :: b₇ :: _ =>
      decodeWord b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
  | _ => 0

end U64

/-- The packed little-endian codec for unsigned 64-bit words. -/
def u64le : WordCodec UInt64 where
  width := 8
  encode := U64.encodeWord
  decode := U64.decodeChunk
  width_pos := by decide
  encode_length := fun _ => rfl
  decode_encode := by
    intro value
    simp only [U64.encodeWord, U64.decodeChunk, U64.decodeWord, UInt64.toUInt8_and,
      show (255 : UInt64).toUInt8 = (-1 : UInt8) from rfl, UInt8.and_neg_one]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
      UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    exact Nat.reassemble64_of_lt value.toNat (UInt64.toNat_lt value)

end Wasm.WordCodec
