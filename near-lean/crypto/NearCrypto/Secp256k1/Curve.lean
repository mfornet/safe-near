import NearCrypto.Secp256k1.PointOps
import NearCrypto.Wnaf

/-!
# secp256k1 in Jacobian coordinates

Points are `(X : Y : Z)` with `x = X / Z²` and `y = Y / Z³`, on `y² = x³ + 7`. The formulas are
`dbl-2009-l`, `madd-2007-bl` and `add-2007-bl`; the exceptional cases (equal or opposite operands,
infinity) are tested explicitly because the arithmetic is in variable time. Scalar multiplication
uses the endomorphism `λ (x, y) = (β x, y)`: both scalars are split into two halves of 128 bits and
four NAF streams (width 5 for the variable point and its image, width 8 over precomputed affine
tables for the base point and its image) share 129 doublings.
-/

namespace NearCrypto.Secp256k1

open Fp

namespace Jac

/-- Doubling (`dbl-2009-l`), with lazy reduction (`PointOps`). -/
def dbl (P : Jac) : Jac :=
  if P.inf then P else dblCore P.x P.y P.z

/-- `P + Q` for an affine `Q` (`madd-2007-bl`). -/
def addAff (P : Jac) (Q : Aff) : Jac :=
  if P.inf then ofAff Q
  else
    let (z1z1, h, r0) := addAffPre P.x P.y P.z Q.x Q.y
    if isZero h then (if isZero r0 then dbl P else infinity) else addAffPost P.x P.y P.z z1z1 h r0

/-- `P + Q` (`add-2007-bl`). -/
def add (P Q : Jac) : Jac :=
  if P.inf then Q
  else
    if Q.inf then P
    else
      let (z1z1, z2z2, u1, s1, h, r0) := addPre P.x P.y P.z Q.x Q.y Q.z
      if isZero h then (if isZero r0 then dbl P else infinity)
      else addPost P.z Q.z z1z1 z2z2 u1 s1 h r0

/-- Doubling (`dbl-2009-l`) with every operation reduced at once: the reference of `dbl`. -/
def dblSimple (P : Jac) : Jac :=
  if P.inf then P
  else
    let a := sq P.x
    let b := sq P.y
    let c := sq b
    let d := mulInt (sub (sub (sq (Fp.add P.x b)) a) c) 2
    let e := mulInt a 3
    let x3 := sub (sq e) (mulInt d 2)
    ⟨x3, sub (mul e (sub d x3)) (mulInt c 8), mulInt (mul P.y P.z) 2, false⟩

/-- `P + Q` for an affine `Q` (`madd-2007-bl`), reduced at once: the reference of `addAff`. -/
def addAffSimple (P : Jac) (Q : Aff) : Jac :=
  if P.inf then ofAff Q
  else
    let z1z1 := sq P.z
    let h := sub (mul Q.x z1z1) P.x
    let r0 := sub (mul (mul Q.y P.z) z1z1) P.y
    if isZero h then (if isZero r0 then dblSimple P else infinity)
    else
      let hh := sq h
      let i := mulInt hh 4
      let j := mul h i
      let r := mulInt r0 2
      let v := mul P.x i
      let x3 := sub (sub (sq r) j) (mulInt v 2)
      ⟨x3, sub (mul r (sub v x3)) (mulInt (mul P.y j) 2), sub (sub (sq (Fp.add P.z h)) z1z1) hh,
        false⟩

/-- `P + Q` (`add-2007-bl`), reduced at once: the reference of `add`. -/
def addSimple (P Q : Jac) : Jac :=
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
      if isZero h then (if isZero r0 then dblSimple P else infinity)
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

/-- The cube root of unity of the field with `λ (x, y) = (β x, y)` (`secp256k1_const_beta`). -/
def beta : Fp :=
  Fp.ofNat 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee

/-- The cube root of unity modulo `n` (`secp256k1_const_lambda`). -/
def lambda : Nat :=
  0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

/-- `k = r1 + r2 λ (mod n)` with `|r1|, |r2| < 2¹²⁸`, as in `secp256k1_scalar_split_lambda`: the
two magnitudes and whether each is the negative of the value. -/
def splitLambda (k : Nat) : (Nat × Bool) × (Nat × Bool) :=
  let g1 := 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031
  let g2 := 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71
  let minusB1 := 0xe4437ed6010e88286f547fa90abfe4c3
  let minusB2 := 0xfffffffffffffffffffffffffffffffe8a280ac50774346dd765cda83db1562c
  let mulShift (a b : Nat) : Nat := ((a * b) >>> 384) + (((a * b) >>> 383) &&& 1)
  let c1 := mulShift k g1 * minusB1 % n
  let c2 := mulShift k g2 * minusB2 % n
  let r2 := (c1 + c2) % n
  let r1 := (k % n + n - r2 * lambda % n) % n
  let high (r : Nat) := r > n / 2
  ((if high r1 then n - r1 else r1, high r1), (if high r2 then n - r2 else r2, high r2))

/-- Odd multiples of the base point up to 127 (width-8 NAF digits), in affine form. -/
def baseTable : Array Aff :=
  batchAffine (oddMultiples (Jac.ofAff Aff.base) 64)

/-- The same multiples of `λ G = (β x, y)`. -/
def baseTableLambda : Array Aff :=
  baseTable.map fun P => ⟨mul beta P.x, P.y⟩

namespace Jac

/-- Add `±digit · P` for the odd `digit` using the Jacobian table of odd multiples; the sign is
flipped when `neg`. -/
@[inline]
def addDigit (R : Jac) (table : Array Jac) (digit : Int) (neg : Bool) : Jac :=
  let digit := if neg then -digit else digit
  if digit > 0 then R.add table[(digit.toNat - 1) / 2]!
  else if digit < 0 then R.add (table[((-digit).toNat - 1) / 2]!).neg else R

/-- Add `±digit · G` (or `· λ G`) using an affine table. -/
@[inline]
def addAffDigit (R : Jac) (table : Array Aff) (digit : Int) (neg : Bool) : Jac :=
  let digit := if neg then -digit else digit
  if digit > 0 then R.addAff table[(digit.toNat - 1) / 2]!
  else if digit < 0 then R.addAff (table[((-digit).toNat - 1) / 2]!).neg else R

/-- Multiples of the point `λ P`, from those of `P`. -/
def mulLambda (P : Jac) : Jac :=
  ⟨mul beta P.x, P.y, P.z, P.inf⟩

/-- The streams of `a · A + b · G` once `a` and `b` are split: from digit `i - 1` down,
`R = 2 R ± a1_j A ± a2_j λ A ± b1_j G ± b2_j λ G`. -/
private def glvLoop (na1 na2 nb1 nb2 : Array Int) (sa1 sa2 sb1 sb2 : Bool) (tA tAL : Array Jac) :
    Nat → Jac → Jac
  | 0, R => R
  | i + 1, R =>
    let R := R.dbl
    let R := R.addDigit tA na1[i]! sa1
    let R := R.addDigit tAL na2[i]! sa2
    let R := R.addAffDigit baseTable nb1[i]! sb1
    glvLoop na1 na2 nb1 nb2 sa1 sa2 sb1 sb2 tA tAL i (R.addAffDigit baseTableLambda nb2[i]! sb2)

/-- `a · A + b · G`, in variable time, with the endomorphism: both scalars are split into two
halves of 128 bits, so the 129 doublings are shared by four width-5 and width-8 NAF streams. -/
def ecmult (a : Nat) (A : Aff) (b : Nat) : Jac :=
  let ((a1, sa1), (a2, sa2)) := splitLambda a
  let ((b1, sb1), (b2, sb2)) := splitLambda b
  let na1 := Wnaf.naf 128 5 a1
  let na2 := Wnaf.naf 128 5 a2
  let nb1 := Wnaf.naf 128 8 b1
  let nb2 := Wnaf.naf 128 8 b2
  let tA := oddMultiples (ofAff A) 8
  glvLoop na1 na2 nb1 nb2 sa1 sa2 sb1 sb2 tA (tA.map mulLambda) 129 infinity

/-- `b · G`. -/
def mulBase (b : Nat) : Jac :=
  let ((b1, sb1), (b2, sb2)) := splitLambda b
  let nb1 := Wnaf.naf 128 8 b1
  let nb2 := Wnaf.naf 128 8 b2
  let rec go : Nat → Jac → Jac
    | 0, R => R
    | i + 1, R =>
      go i (((R.dbl).addAffDigit baseTable nb1[i]! sb1).addAffDigit baseTableLambda nb2[i]! sb2)
  go 129 infinity

end Jac

end NearCrypto.Secp256k1
