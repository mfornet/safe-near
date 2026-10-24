import NearCrypto.Bytes

/-!
# The prime and the scalar field

`p = 2²⁵⁵ − 19` is the field prime, `ℓ` the order of the base point. Scalars are `Nat`s below
`ℓ` (or, for the clamped secret scalar, below `2²⁵⁵`); their arithmetic is a product and a `%` on
numbers of at most 512 bits, a handful per signature, so `Nat` is the right representation.
Nothing here is constant time: verification handles public data only; a signing implementation
for secret keys would need different code (design notes, M2).
-/

namespace NearCrypto.Ed25519

/-- The field prime `2²⁵⁵ − 19`. -/
def p : Nat :=
  2 ^ 255 - 19

/-- The order `ℓ` of the base point. -/
def ell : Nat :=
  2 ^ 252 + 27742317777372353535851937790883648493

namespace Scalar

/-- The little-endian value of the `words` 64-bit words of `b` at byte offset `off`. -/
def ofBytes (b : ByteArray) (off words : Nat) : Nat :=
  (List.range words).foldr (fun i n => n <<< 64 ||| (le64 b (off + 8 * i)).toNat) 0

/-- Little-endian 32-byte encoding of `x < 2²⁵⁶`. -/
def toBytes32 (x : Nat) : ByteArray :=
  pushLe64
    (pushLe64 (pushLe64 (pushLe64 ByteArray.empty x.toUInt64) (x >>> 64).toUInt64)
      (x >>> 128).toUInt64)
    (x >>> 192).toUInt64

/-- A 64-byte hash read as a number and reduced modulo `ℓ`. -/
def reduceWide (h : ByteArray) : Nat :=
  ofBytes h 0 8 % ell

end Scalar

end NearCrypto.Ed25519
