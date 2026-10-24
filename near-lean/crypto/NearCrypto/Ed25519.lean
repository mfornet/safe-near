import NearCrypto.Ed25519.Curve
import NearCrypto.Ed25519.Spec
import NearCrypto.Sha512

/-!
# Ed25519

`verify` accepts exactly what `near-crypto` 0.37.4 accepts through
`ed25519-dalek` 2.2.0 (see `Ed25519.Spec` for the rules and their sources).
`SigningKey` is the `ED25519SecretKey` of `near-crypto`: the 32-byte seed
followed by the 32-byte public key (`keypair` below).
-/

namespace NearCrypto.Ed25519

/-! ### Impl -/

namespace Impl

open Ext

/-- Whether the 32 bytes decode to a point (`VerifyingKey::from_bytes`). -/
def validPublicKey (pk : ByteArray) : Bool :=
  (decompress pk).isSome

/-- `near_crypto::Signature::verify` for an ED25519 key and signature. -/
def verify (pk msg sig : ByteArray) : Bool :=
  if pk.size != 32 || sig.size != 64 then false
  else
    match decompress pk with
    | none => false
    | some A =>
      let rBytes := sig.extract 0 32
      let s := Scalar.ofBytes sig 32 4
      if s ≥ ell then false
      else
        let k := Scalar.reduceWide (Sha512.Impl.hash (rBytes ++ pk ++ msg))
        compress (doubleMulBase k (neg A) s) == rBytes

/-- A signing key: the clamped scalar, the nonce prefix and the public key. -/
structure SigningKey where
  scalar : Nat
  prefix_ : ByteArray
  publicKey : ByteArray
  deriving Inhabited

/-- Expand a 32-byte seed (`ExpandedSecretKey::from_bytes`): hash, clamp and reduce. -/
def SigningKey.ofSeed (seed : ByteArray) : Option SigningKey :=
  if seed.size != 32 then none
  else
    let h := Sha512.Impl.hash seed
    let a := Scalar.ofBytes h 0 4
    let a := (a % 2 ^ 254) / 8 * 8 + 2 ^ 254
    some { scalar := a, prefix_ := h.extract 32 64, publicKey := compress (mulBase a) }

/-- The 64-byte `keypair` layout; `none` unless the public half is the one the seed derives
(`SigningKey::from_keypair_bytes`). -/
def SigningKey.ofKeypair (keypair : ByteArray) : Option SigningKey :=
  if keypair.size != 64 then none
  else
    match SigningKey.ofSeed (keypair.extract 0 32) with
    | some k => if k.publicKey == keypair.extract 32 64 then some k else none
    | none => none

/-- Deterministic RFC 8032 signature. -/
def SigningKey.sign (k : SigningKey) (msg : ByteArray) : ByteArray :=
  let r := Scalar.reduceWide (Sha512.Impl.hash (k.prefix_ ++ msg))
  let R := compress (mulBase r)
  let h := Scalar.reduceWide (Sha512.Impl.hash (R ++ k.publicKey ++ msg))
  R ++ Scalar.toBytes32 ((r + h * k.scalar) % ell)

end Impl

end NearCrypto.Ed25519

namespace NearCrypto

/-- `near_crypto::Signature::verify` for ED25519: public key (32 bytes), message, signature (64
bytes). -/
def ed25519Verify (pk msg sig : ByteArray) : Bool :=
  Ed25519.Impl.verify pk msg sig

end NearCrypto
