import NearCrypto.Secp256k1.FpMul

/-!
# secp256k1 points

Affine and Jacobian points, and the field exponentiations they need: the inverse and the square
root, by the addition chains of `libsecp256k1` (`p - 2` and `(p + 1) / 4` share their blocks of
ones).
-/

namespace NearCrypto.Secp256k1

namespace Fp

/-- `a ^ (2 ^ k)`. -/
def pow2k (a : Fp) : Nat → Fp
  | 0 => a
  | k + 1 => pow2k (sq a) k

/-- `(a ^ 3, a ^ (2 ^ 22 - 1), a ^ (2 ^ 223 - 1), a ^ (2 ^ 2 - 1))`, the blocks of ones in
`p - 2` and `(p + 1) / 4`. -/
def blocks (a : Fp) : Fp × Fp × Fp × Fp :=
  let x2 := mul (sq a) a
  let x3 := mul (sq x2) a
  let x6 := mul (pow2k x3 3) x3
  let x9 := mul (pow2k x6 3) x3
  let x11 := mul (pow2k x9 2) x2
  let x22 := mul (pow2k x11 11) x11
  let x44 := mul (pow2k x22 22) x22
  let x88 := mul (pow2k x44 44) x44
  let x176 := mul (pow2k x88 88) x88
  let x220 := mul (pow2k x176 44) x44
  let x223 := mul (pow2k x220 3) x3
  (x3, x22, x223, x2)

/-- `a ^ (p - 2)`, the inverse (zero for zero). -/
def inv (a : Fp) : Fp :=
  let (_, x22, x223, x2) := blocks a
  let t := mul (pow2k x223 23) x22
  let t := mul (pow2k t 5) a
  let t := mul (pow2k t 3) x2
  mul (pow2k t 2) a

/-- `a ^ ((p + 1) / 4)`: a square root of `a` when `a` is a square. -/
def sqrtCandidate (a : Fp) : Fp :=
  let (_, x22, x223, x2) := blocks a
  let t := mul (pow2k x223 23) x22
  let t := mul (pow2k t 6) x2
  pow2k t 2

/-- A square root of `a` when there is one. -/
def sqrt (a : Fp) : Option Fp :=
  let r := sqrtCandidate a
  if eq (sq r) a then some r else none

/-- `x³ + 7`. -/
def curveRhs (x : Fp) : Fp :=
  add (mul (sq x) x) (ofNat 7)

end Fp

open Fp

/-- An affine point. -/
structure Aff where
  x : Fp
  y : Fp
  deriving Inhabited

/-- A Jacobian point; `inf` is the point at infinity. -/
structure Jac where
  x : Fp
  y : Fp
  z : Fp
  inf : Bool
  deriving Inhabited

namespace Aff

/-- The base point. -/
def base : Aff :=
  ⟨Fp.ofNat 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
    Fp.ofNat 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8⟩

/-- Whether the point is on the curve. -/
def onCurve (P : Aff) : Bool :=
  eq (sq P.y) (curveRhs P.x)

/-- The negative of a point. -/
def neg (P : Aff) : Aff :=
  ⟨P.x, Fp.neg P.y⟩

end Aff

namespace Jac

/-- The point at infinity. -/
def infinity : Jac :=
  ⟨zero, one, zero, true⟩

/-- Lift an affine point. -/
def ofAff (P : Aff) : Jac :=
  ⟨P.x, P.y, one, false⟩

/-- The negative of a point. -/
def neg (P : Jac) : Jac :=
  ⟨P.x, Fp.neg P.y, P.z, P.inf⟩

end Jac

end NearCrypto.Secp256k1
