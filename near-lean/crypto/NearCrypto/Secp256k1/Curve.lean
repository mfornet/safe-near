import NearCrypto.Secp256k1.FpMul
import NearCrypto.Wnaf

/-!
# secp256k1 in Jacobian coordinates

Points are `(X : Y : Z)` with `x = X / Z²` and `y = Y / Z³`, on `y² = x³ + 7`. The formulas are
`dbl-2009-l`, `madd-2007-bl` and `add-2007-bl`; the exceptional cases (equal or opposite operands,
infinity) are tested explicitly because the arithmetic is in variable time. Scalar multiplication
is a width-5 NAF for a variable point and a width-8 NAF over a precomputed affine table for the
base point, joined by Shamir's trick.
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

/-- Doubling (`dbl-2009-l`). -/
def dbl (P : Jac) : Jac :=
  if P.inf then P
  else
    let a := sq P.x
    let b := sq P.y
    let c := sq b
    let d := mulInt (sub (sub (sq (Fp.add P.x b)) a) c) 2
    let e := mulInt a 3
    let x3 := sub (sq e) (mulInt d 2)
    ⟨x3, sub (mul e (sub d x3)) (mulInt c 8), mulInt (mul P.y P.z) 2, false⟩

/-- `P + Q` for an affine `Q` (`madd-2007-bl`). -/
def addAff (P : Jac) (Q : Aff) : Jac :=
  if P.inf then ofAff Q
  else
    let z1z1 := sq P.z
    let h := sub (mul Q.x z1z1) P.x
    let r0 := sub (mul (mul Q.y P.z) z1z1) P.y
    if isZero h then (if isZero r0 then dbl P else infinity)
    else
      let hh := sq h
      let i := mulInt hh 4
      let j := mul h i
      let r := mulInt r0 2
      let v := mul P.x i
      let x3 := sub (sub (sq r) j) (mulInt v 2)
      ⟨x3, sub (mul r (sub v x3)) (mulInt (mul P.y j) 2), sub (sub (sq (Fp.add P.z h)) z1z1) hh,
        false⟩

/-- `P + Q` (`add-2007-bl`). -/
def add (P Q : Jac) : Jac :=
  if P.inf then Q
  else
    if Q.inf then P
    else
      let z1z1 := sq P.z
      let z2z2 := sq Q.z
      let u1 := mul P.x z2z2
      let h := sub (mul Q.x z1z1) u1
      let s1 := mul (mul P.y Q.z) z2z2
      let r0 := sub (mul (mul Q.y P.z) z1z1) s1
      if isZero h then (if isZero r0 then dbl P else infinity)
      else
        let i := sq (mulInt h 2)
        let j := mul h i
        let r := mulInt r0 2
        let v := mul u1 i
        let x3 := sub (sub (sq r) j) (mulInt v 2)
        ⟨x3, sub (mul r (sub v x3)) (mulInt (mul s1 j) 2),
          mul (sub (sub (sq (Fp.add P.z Q.z)) z1z1) z2z2) h, false⟩

/-- The affine point; `none` for infinity. -/
def toAff (P : Jac) : Option Aff :=
  if P.inf then none
  else
    let zi := inv P.z
    let zi2 := sq zi
    some ⟨mul P.x zi2, mul P.y (mul zi2 zi)⟩

end Jac

/-- Affine forms of finite Jacobian points, with one inversion for all of them. -/
def batchAffine (ps : Array Jac) : Array Aff :=
  Id.run do
    let mut prefixes : Array Fp := Array.mkEmpty ps.size
    let mut acc := one
    for P in ps do
      prefixes := prefixes.push acc
      acc := mul acc P.z
    let mut inverse := inv acc
    let mut out : Array Aff := Array.replicate ps.size default
    for i in (List.range ps.size).reverse do
      let P := ps[i]!
      let zi := mul inverse prefixes[i]!
      inverse := mul inverse P.z
      let zi2 := sq zi
      out := out.set! i ⟨mul P.x zi2, mul P.y (mul zi2 zi)⟩
    return out

/-- The odd multiples `P, 3 P, …, (2 count - 1) P`. -/
def oddMultiples (P : Jac) (count : Nat) : Array Jac :=
  let P2 := P.dbl
  let rec go : Nat → Jac → Array Jac → Array Jac
    | 0, _, t => t
    | k + 1, last, t =>
      let next := last.add P2
      go k next (t.push next)
  go (count - 1) P #[P]

/-- Odd multiples of the base point up to 255 (width-8 NAF digits), in affine form. -/
def baseTable : Array Aff :=
  batchAffine (oddMultiples (Jac.ofAff Aff.base) 128)

namespace Jac

/-- Add `digit · P` for the odd `digit` using the Jacobian table of odd multiples. -/
@[inline]
def addDigit (R : Jac) (table : Array Jac) (digit : Int) : Jac :=
  if digit > 0 then R.add table[(digit.toNat - 1) / 2]!
  else if digit < 0 then R.add (table[((-digit).toNat - 1) / 2]!).neg else R

/-- Add `digit · G` using the affine table of the base point. -/
@[inline]
def addBaseDigit (R : Jac) (digit : Int) : Jac :=
  if digit > 0 then R.addAff baseTable[(digit.toNat - 1) / 2]!
  else if digit < 0 then R.addAff (baseTable[((-digit).toNat - 1) / 2]!).neg else R

/-- Shamir's trick from digit `i - 1` down: `R = 2 R + a_j A + b_j G`. -/
private def shamir (nafA nafB : Array Int) (tableA : Array Jac) : Nat → Jac → Jac
  | 0, R => R
  | i + 1, R =>
    let R := R.dbl
    let R := R.addDigit tableA nafA[i]!
    shamir nafA nafB tableA i (R.addBaseDigit nafB[i]!)

/-- `a · A + b · G` for `a, b < 2²⁵⁶`, in variable time. -/
def ecmult (a : Nat) (A : Aff) (b : Nat) : Jac :=
  let nafA := Wnaf.naf 256 5 a
  let nafB := Wnaf.naf 256 8 b
  let top := ((List.range 257).reverse.find? fun i => nafA[i]! != 0 || nafB[i]! != 0).getD 0
  shamir nafA nafB (oddMultiples (ofAff A) 8) (top + 1) infinity

/-- `b · G` for `b < 2²⁵⁶`. -/
def mulBase (b : Nat) : Jac :=
  let nafB := Wnaf.naf 256 8 b
  let rec go : Nat → Jac → Jac
    | 0, R => R
    | i + 1, R => go i ((R.dbl).addBaseDigit nafB[i]!)
  go 257 infinity

end Jac

end NearCrypto.Secp256k1
