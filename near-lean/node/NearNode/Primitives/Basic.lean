import NearNode.Borsh
import NearCrypto.Sha256

/-!
# Scalars, hashes, account ids and keys

`near-primitives-core` and `near-crypto` at `=0.37.4`. Byte strings are
`ByteArray`; their lengths are fixed by the decoders.
-/

namespace Near.Node

open Borsh

/-- `Balance` (`NearToken`): a `u128` of yoctoNEAR. -/
abbrev Balance :=
  U128

/-- `Gas`: a `u64`. -/
abbrev Gas :=
  UInt64

abbrev Nonce :=
  UInt64

/-- `NonceIndex`: a `u16`. -/
abbrev NonceIndex :=
  UInt16

abbrev BlockHeight :=
  UInt64

/-- `ShardId`: a `u64` newtype. -/
abbrev ShardId :=
  UInt64

abbrev StorageUsage :=
  UInt64

abbrev ProtocolVersion :=
  UInt32

/-- `CryptoHash`: 32 bytes. -/
structure CryptoHash where
  bytes : ByteArray
  deriving BEq, Inhabited

instance : Codec CryptoHash :=
  .isoOf (.fixed 32) .mk CryptoHash.bytes

namespace CryptoHash

/-- The zero hash. -/
def zero : CryptoHash :=
  ⟨ByteArray.mk (Array.replicate 32 0)⟩

/-- SHA-256 of `data`. -/
def hash (data : ByteArray) : CryptoHash :=
  ⟨NearCrypto.sha256 data⟩

/-- Hash of the Borsh encoding of `a`. -/
def hashBorsh [Codec α] (a : α) : CryptoHash :=
  hash (Codec.encode a)

end CryptoHash

/-- An account id: 2 to 64 bytes of `a-z0-9` separated by single `-`, `_` or `.`. -/
structure AccountId where
  val : String
  deriving BEq, Inhabited, Repr

namespace AccountId

/-- The validity rules of `near-account-id`. -/
def isValid (s : String) : Bool :=
  let isSep (c : Char) := c == '-' || c == '_' || c == '.'
  let isAlnum (c : Char) := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
  let rec go : List Char → Bool → Bool
    | [], lastSep => !lastSep
    | c :: cs, lastSep =>
      if isAlnum c then go cs false else if isSep c then !lastSep && go cs true else false
  2 ≤ s.utf8ByteSize && s.utf8ByteSize ≤ 64 && go s.toList true

end AccountId

/-- Borsh encodes an account id as a `String` and checks its validity when decoding. -/
instance : Codec AccountId :=
  .tryIsoOf (inferInstanceAs (Codec String))
    (fun s => if AccountId.isValid s then .ok ⟨s⟩ else .error (.invalid "AccountId")) AccountId.val

/-- `near_crypto::PublicKey`; the payload lengths are 32, 64 and 1952. -/
inductive PublicKey where
  | ed25519 (key : ByteArray)
  | secp256k1 (key : ByteArray)
  | mldsa65 (key : ByteArray)
  deriving BEq, Inhabited

instance : Codec PublicKey :=
  .enum "PublicKey"
    [.variantOf 0 (.fixed 32) .ed25519 fun
        | .ed25519 k => some k
        | _ => none,
      .variantOf 1 (.fixed 64) .secp256k1 fun
        | .secp256k1 k => some k
        | _ => none,
      .variantOf 2 (.fixed 1952) .mldsa65 fun
        | .mldsa65 k => some k
        | _ => none]

/-- `near_crypto::Signature`; the payload lengths are 64, 65 and 3309. -/
inductive Signature where
  | ed25519 (sig : ByteArray)
  | secp256k1 (sig : ByteArray)
  | mldsa65 (sig : ByteArray)
  deriving BEq, Inhabited

/-- Ed25519 signatures whose last byte has any of the top three bits set are rejected. -/
@[instance_reducible]
private def ed25519Signature : Codec ByteArray :=
  .tryIsoOf (.fixed 64)
    (fun b => if b[63]! &&& 0xE0 != 0 then .error (.invalid "signature") else .ok b) id

instance : Codec Signature :=
  .enum "Signature"
    [.variantOf 0 ed25519Signature .ed25519 fun
        | .ed25519 k => some k
        | _ => none,
      .variantOf 1 (.fixed 65) .secp256k1 fun
        | .secp256k1 k => some k
        | _ => none,
      .variantOf 2 (.fixed 3309) .mldsa65 fun
        | .mldsa65 k => some k
        | _ => none]

end Near.Node
