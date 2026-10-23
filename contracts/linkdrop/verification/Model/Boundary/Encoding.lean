import NearInterface.Json

/-!
# Text encodings linkdrop reads

The argument types of linkdrop's methods, as near-sdk 5.17.1 deserialises
them from JSON strings:

* `PublicKey`: an optional curve prefix (`ed25519:` or `secp256k1:`, ASCII
  case-insensitive, `ed25519` when absent) and base58 key bytes, 32 or 64 of
  them (`near_sdk::types::public_key`);
* `Base58CryptoHash`: base58, exactly 32 bytes;
* `Base64VecU8`: base64 with the standard alphabet and canonical padding
  (`base64::engine::general_purpose::STANDARD`);
* `Vec<u8>`: an array of JSON integers in `0..=255`.

Base58 is the bs58 crate's Bitcoin alphabet: each leading `1` is a zero byte,
the rest is a big-endian number.
-/

namespace Linkdrop.Boundary

open NearInterface.Json

abbrev Bytes := List UInt8

/-! ## Base58 -/

def base58Alphabet : List Char :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList

def base58Digit (c : Char) : Option Nat := base58Alphabet.idxOf? c

/-- Big-endian bytes of `n`, none for `0`. -/
def natBytesBE (n : Nat) : Bytes :=
  if _h : n = 0 then [] else natBytesBE (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n
decreasing_by omega

def base58Decode (s : String) : Option Bytes := do
  let digits ← s.toList.mapM base58Digit
  let zeros := (digits.takeWhile (· == 0)).length
  let value := digits.foldl (fun n d => n * 58 + d) 0
  pure (List.replicate zeros 0 ++ natBytesBE value)

/-! ## Base64 -/

def base64Alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

def base64Digit (c : Char) : Option Nat := base64Alphabet.idxOf? c

/-- One group of four symbols, the last one possibly padded. Unused bits of
the last symbol must be zero. -/
def base64Group (last : Bool) : List Char → Option Bytes
  | [a, b, '=', '='] => do
    guard last
    let a ← base64Digit a
    let b ← base64Digit b
    guard (b % 16 = 0)
    pure [UInt8.ofNat (a * 4 + b / 16)]
  | [a, b, c, '='] => do
    guard last
    let a ← base64Digit a
    let b ← base64Digit b
    let c ← base64Digit c
    guard (c % 4 = 0)
    pure [UInt8.ofNat (a * 4 + b / 16), UInt8.ofNat (b % 16 * 16 + c / 4)]
  | [a, b, c, d] => do
    let a ← base64Digit a
    let b ← base64Digit b
    let c ← base64Digit c
    let d ← base64Digit d
    pure [UInt8.ofNat (a * 4 + b / 16), UInt8.ofNat (b % 16 * 16 + c / 4), UInt8.ofNat (c % 4 * 64 + d)]
  | _ => none

def base64Groups : List Char → Option Bytes
  | [] => some []
  | a :: b :: c :: d :: rest => do
    let bytes ← base64Group rest.isEmpty [a, b, c, d]
    let tail ← base64Groups rest
    pure (bytes ++ tail)
  | _ => none

def base64Decode (s : String) : Option Bytes := base64Groups s.toList

/-! ## Public keys -/

/-- SDK `PublicKey` data: a curve tag, then 32 (ed25519) or 64 (secp256k1) bytes. -/
def validKeyData (data : Bytes) : Bool :=
  (data.head? == some 0 && data.length == 33) || (data.head? == some 1 && data.length == 65)

abbrev PublicKey := { data : Bytes // validKeyData data = true }

def PublicKey.ofData? (data : Bytes) : Option PublicKey :=
  if h : validKeyData data = true then some ⟨data, h⟩ else none

/-- `CurveType::from_str`: `eq_ignore_ascii_case`. -/
def curveOf (prefix_ : String) : Option (UInt8 × Nat) :=
  let lower := String.ofList (prefix_.toList.map Char.toLower)
  if lower == "ed25519" then some (0, 32)
  else if lower == "secp256k1" then some (1, 64)
  else none

/-- `PublicKey::from_str`: split at the first `:`, base58 decode, check the length. -/
def publicKeyOfString (s : String) : Option PublicKey := do
  let chars := s.toList
  let (curve, len, data) ← match chars.idxOf? ':' with
    | some i => do
      let (tag, len) ← curveOf (String.ofList (chars.take i))
      pure (tag, len, String.ofList (chars.drop (i + 1)))
    | none => pure (0, 32, s)
  let bytes ← base58Decode data
  guard (bytes.length = len)
  PublicKey.ofData? (curve :: bytes)

/-! ## JSON field decoders -/

def publicKey (v : Value) : Option PublicKey := (string v).bind publicKeyOfString

def cryptoHash (v : Value) : Option Bytes := do
  let bytes ← (string v).bind base58Decode
  guard (bytes.length = 32)
  pure bytes

def base64Bytes (v : Value) : Option Bytes := (string v).bind base64Decode

/-- A `u8` from a JSON integer: digits only (a sign, fraction or exponent
makes it a float or negative), at most 255. -/
def byte (v : Value) : Option UInt8 := do
  let .number text := v | none
  let n ← text.toNat?
  guard (n < 256)
  pure (UInt8.ofNat n)

def array (decode : Value → Option α) : Value → Option (List α)
  | .arr vs => vs.mapM decode
  | _ => none

/-- `NearToken`: a JSON string holding a decimal `u128`. -/
abbrev token := u128

end Linkdrop.Boundary
