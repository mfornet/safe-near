/-!
# Byte helpers

Big- and little-endian word loads and stores over `ByteArray`, and hex.
-/

namespace NearCrypto

/-- The big-endian `UInt32` at byte offset `i` (the caller guarantees `i + 4 ≤ b.size`). -/
@[inline]
def be32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 <<< 24 ||| (b.get! (i + 1)).toUInt32 <<< 16 |||
    (b.get! (i + 2)).toUInt32 <<< 8 |||
    (b.get! (i + 3)).toUInt32

/-- The little-endian `UInt32` at byte offset `i`. -/
@[inline]
def le32 (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! (i + 3)).toUInt32 <<< 24 ||| (b.get! (i + 2)).toUInt32 <<< 16 |||
    (b.get! (i + 1)).toUInt32 <<< 8 |||
    (b.get! i).toUInt32

/-- The big-endian `UInt64` at byte offset `i`. -/
@[inline]
def be64 (b : ByteArray) (i : Nat) : UInt64 :=
  (be32 b i).toUInt64 <<< 32 ||| (be32 b (i + 4)).toUInt64

/-- The little-endian `UInt64` at byte offset `i`. -/
@[inline]
def le64 (b : ByteArray) (i : Nat) : UInt64 :=
  (le32 b (i + 4)).toUInt64 <<< 32 ||| (le32 b i).toUInt64

/-- Append `x` big-endian. -/
@[inline]
def pushBe32 (b : ByteArray) (x : UInt32) : ByteArray :=
  (((b.push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push x.toUInt8

/-- Append `x` little-endian. -/
@[inline]
def pushLe32 (b : ByteArray) (x : UInt32) : ByteArray :=
  (((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

/-- Append `x` big-endian. -/
@[inline]
def pushBe64 (b : ByteArray) (x : UInt64) : ByteArray :=
  pushBe32 (pushBe32 b (x >>> 32).toUInt32) x.toUInt32

/-- Append `x` little-endian. -/
@[inline]
def pushLe64 (b : ByteArray) (x : UInt64) : ByteArray :=
  pushLe32 (pushLe32 b x.toUInt32) (x >>> 32).toUInt32

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n 0)

/-- Lowercase hex. -/
def toHex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat)
  b.foldl (fun s x => (s.push (digit (x >>> 4))).push (digit (x &&& 15))) ""

/-- Parse hex; `none` on odd length or a non-hex character. -/
def ofHex (s : String) : Option ByteArray := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then
    none
  let nibble (c : Char) : Option UInt8 :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48).toUInt8
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87).toUInt8 else none
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push ((← nibble cs[2 * i]!) <<< 4 ||| (← nibble cs[2 * i + 1]!))
  pure out

end NearCrypto
