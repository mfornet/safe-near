import NearCrypto.Sha256

/-!
# HMAC-SHA256 (RFC 2104)

The pseudorandom function of `libsecp256k1`'s RFC 6979 nonce (`Secp256k1`). `Spec` and `Impl`
differ only in the SHA-256 they call.
-/

namespace NearCrypto.Hmac

/-- HMAC over `hash` with `block`-byte blocks. -/
def hmac (hash : ByteArray → ByteArray) (block : Nat) (key msg : ByteArray) : ByteArray :=
  let key := if key.size > block then hash key else key
  let key := key ++ zeros (block - key.size)
  let pad (c : UInt8) : ByteArray := ⟨key.data.map (· ^^^ c)⟩
  hash (pad 0x5c ++ hash (pad 0x36 ++ msg))

namespace Spec

/-- HMAC-SHA256 over the reference SHA-256. -/
def sha256 (key msg : ByteArray) : ByteArray :=
  hmac Sha256.Spec.hash 64 key msg

end Spec

namespace Impl

/-- HMAC-SHA256 over the fast SHA-256. -/
def sha256 (key msg : ByteArray) : ByteArray :=
  hmac Sha256.Impl.hash 64 key msg

end Impl

end NearCrypto.Hmac
