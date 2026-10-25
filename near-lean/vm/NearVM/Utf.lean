/-!
# UTF-8 validation and UTF-16LE decoding

The string host functions (`log_utf8`, `log_utf16`, `panic_utf8`, `abort`) read guest bytes as
UTF-8 or UTF-16LE. These are the two pure functions they need, written over `List UInt8` with no
imports so that the VM and the contract proofs can use them freely:

* `validUtf8` is `core::str::from_utf8` succeeding (no overlong forms, surrogates or code points
  above `U+10FFFF`);
* `decodeUtf16LE` is `char::decode_utf16` over the little-endian code units, collected into a
  `String`, re-encoded as UTF-8 (surrogate pairs combine, an unpaired surrogate fails). An odd
  number of bytes is not decoded here; the host function rejects it first.
-/

namespace Wasm.Near

private def inRange (b : UInt8) (lo hi : Nat) : Bool := decide (lo ≤ b.toNat ∧ b.toNat ≤ hi)

/-- `core::str::from_utf8(bytes).is_ok()`, by the well-formed byte sequences of Unicode
(Table 3-7). -/
def validUtf8 : List UInt8 → Bool
  | [] => true
  | b0 :: rest =>
    if b0.toNat < 0x80 then validUtf8 rest
    else if inRange b0 0xC2 0xDF then
      match rest with
      | b1 :: rest' => inRange b1 0x80 0xBF && validUtf8 rest'
      | _ => false
    else if inRange b0 0xE0 0xEF then
      match rest with
      | b1 :: b2 :: rest' =>
        (if b0.toNat = 0xE0 then inRange b1 0xA0 0xBF
         else if b0.toNat = 0xED then inRange b1 0x80 0x9F
         else inRange b1 0x80 0xBF) && inRange b2 0x80 0xBF && validUtf8 rest'
      | _ => false
    else if inRange b0 0xF0 0xF4 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        (if b0.toNat = 0xF0 then inRange b1 0x90 0xBF
         else if b0.toNat = 0xF4 then inRange b1 0x80 0x8F
         else inRange b1 0x80 0xBF) && inRange b2 0x80 0xBF && inRange b3 0x80 0xBF &&
          validUtf8 rest'
      | _ => false
    else false

/-- The UTF-8 encoding of a Unicode scalar value (callers pass only scalar values). -/
def encodeUtf8 (cp : Nat) : List UInt8 :=
  if cp < 0x80 then [UInt8.ofNat cp]
  else if cp < 0x800 then [UInt8.ofNat (0xC0 + cp / 64), UInt8.ofNat (0x80 + cp % 64)]
  else if cp < 0x10000 then
    [UInt8.ofNat (0xE0 + cp / 4096), UInt8.ofNat (0x80 + cp / 64 % 64), UInt8.ofNat (0x80 + cp % 64)]
  else
    [UInt8.ofNat (0xF0 + cp / 262144), UInt8.ofNat (0x80 + cp / 4096 % 64),
     UInt8.ofNat (0x80 + cp / 64 % 64), UInt8.ofNat (0x80 + cp % 64)]

/-- A UTF-8 byte sequence as a `String` (empty if it is not valid). -/
def utf8String (bytes : List UInt8) : String :=
  (String.fromUTF8? ⟨bytes.toArray⟩).getD ""

/-- Little-endian 16-bit code units; `none` for an odd number of bytes. -/
def utf16Units : List UInt8 → Option (List Nat)
  | [] => some []
  | [_] => none
  | lo :: hi :: rest => (utf16Units rest).map fun units => (lo.toNat + 256 * hi.toNat) :: units

/-- `char::decode_utf16` collected into a `String`, as UTF-8 bytes: `none` on an unpaired
surrogate. -/
def decodeUtf16Units : List Nat → Option (List UInt8)
  | [] => some []
  | u :: rest =>
    if u < 0xD800 ∨ 0xE000 ≤ u then (decodeUtf16Units rest).map (encodeUtf8 u ++ ·)
    else if u < 0xDC00 then
      match rest with
      | v :: rest' =>
        if 0xDC00 ≤ v ∧ v < 0xE000 then
          (decodeUtf16Units rest').map
            (encodeUtf8 (0x10000 + (u - 0xD800) * 1024 + (v - 0xDC00)) ++ ·)
        else none
      | [] => none
    else none

/-- UTF-16LE bytes to UTF-8 bytes; `none` for an odd length or an unpaired surrogate. -/
def decodeUtf16LE (bytes : List UInt8) : Option (List UInt8) :=
  (utf16Units bytes).bind decodeUtf16Units

end Wasm.Near
