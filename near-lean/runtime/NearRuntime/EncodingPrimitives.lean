import NearRuntime.Types

/-! Borsh primitives shared by the state, receipt, queue and transaction
encoders, so their integer, length-prefix and duplicate checks cannot drift. -/
namespace Near.EncodingPrimitives

/-- Little-endian `width`-byte encoding of `value`, truncated to that width. -/
def little (width value : Nat) : Bytes :=
  (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

/-- Borsh `u{8 * width}`; values that do not fit are rejected. -/
def unsigned (width value : Nat) : Except String Bytes :=
  if value < 2 ^ (8 * width) then pure (little width value)
  else throw s!"integer exceeds u{8 * width}"

/-- Borsh `Vec<u8>`: a `u32` length, then the bytes. -/
def vector (bytes : Bytes) : Except String Bytes := do
  return (← unsigned 4 bytes.length) ++ bytes

/-- Borsh `String`: its UTF-8 bytes as a vector. -/
def string (text : String) : Except String Bytes := vector text.toUTF8.toList

/-- Borsh `Vec<T>`: a `u32` count, then each encoded element. -/
def sequence (encode : α → Except String Bytes) (values : List α) : Except String Bytes := do
  return (← unsigned 4 values.length) ++ (← values.mapM encode).flatten

/-- Fail on a repeated value; `name` describes what is repeated. -/
def unique [BEq α] (name : String) (values : List α) : Except String Unit := do
  unless values.eraseDups.length == values.length do throw s!"duplicate {name}"

end Near.EncodingPrimitives
