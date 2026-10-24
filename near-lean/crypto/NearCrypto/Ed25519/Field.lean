import NearCrypto.Bytes

/-!
# GF(2²⁵⁵ − 19) and the scalar field

Field elements are `Nat`s below `p`. Lean's `Nat` is GMP-backed once a value
exceeds 63 bits, so a product and one `%` is a single multiplication and a
single division of 510 by 255 bits; `Ed25519.md` in the design notes records
the benchmark against folding the high half and against limb arithmetic.
Only `mul` and `sq` reduce: `add` and `sub` are plain `Nat` operations whose
results (below `4p`) feed the next product, so the representation never needs
a conditional subtraction. Nothing here is constant time. Verification handles
public data only; a signing implementation for secret keys would need a
different one (design notes, M2).
-/

namespace NearCrypto.Ed25519

/-- The field prime `2²⁵⁵ − 19`. -/
def p : Nat :=
  2 ^ 255 - 19

/-- The order `ℓ` of the base point. -/
def ell : Nat :=
  2 ^ 252 + 27742317777372353535851937790883648493

namespace Field

/-- Product, reduced. -/
@[inline]
def mul (a b : Nat) : Nat :=
  a * b % p

/-- Square, reduced. -/
@[inline]
def sq (a : Nat) : Nat :=
  a * a % p

/-- `a ^ (2 ^ k)`. -/
def pow2k (a : Nat) : Nat → Nat
  | 0 => a
  | k + 1 => pow2k (sq a) k

/-- `(a ^ (2 ^ 250 - 1), a ^ 11)`: the common prefix of the inversion and square-root chains. -/
def pow250 (a : Nat) : Nat × Nat :=
  let z2 := sq a
  let z9 := mul a (pow2k z2 2)
  let z11 := mul z2 z9
  let z5 := mul z9 (sq z11)
  let z10 := mul (pow2k z5 5) z5
  let z20 := mul (pow2k z10 10) z10
  let z40 := mul (pow2k z20 20) z20
  let z50 := mul (pow2k z40 10) z10
  let z100 := mul (pow2k z50 50) z50
  let z200 := mul (pow2k z100 100) z100
  (mul (pow2k z200 50) z50, z11)

/-- `a ^ (p - 2)`, the inverse (zero for zero). -/
def inv (a : Nat) : Nat :=
  let (z250, z11) := pow250 a
  mul (pow2k z250 5) z11

/-- `a ^ ((p - 5) / 8) = a ^ (2 ^ 252 - 3)`. -/
def powP58 (a : Nat) : Nat :=
  mul (pow2k (pow250 a).1 2) a

/-- A square root of `−1`. -/
def sqrtM1 : Nat :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- The curve constant `d = −121665 / 121666`. -/
def d : Nat :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `2 d`. -/
def d2 : Nat :=
  2 * d % p

/-- A root of `u / v` when there is one (the form `sqrt_ratio_i` of `curve25519-dalek`). -/
def sqrtRatio (u v : Nat) : Option Nat :=
  let v3 := mul (sq v) v
  let v7 := mul (sq v3) v
  let r := mul (mul u v3) (powP58 (mul u v7))
  let c := mul v (sq r)
  let nu := (p - u % p) % p
  if c = u % p then some r else if c = nu then some (mul r sqrtM1) else none

end Field

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
