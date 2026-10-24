import NearCrypto.Ed25519.Field

/-!
# edwards25519 in extended coordinates

Points are `(X : Y : Z : T)` with `x = X/Z`, `y = Y/Z` and `T = X Y / Z`. The
formulas are `add-2008-hwcd-3` and `dbl-2008-hwcd` for `a = −1`; both are
complete on this curve. Scalar multiplication is a width-5 NAF for variable
points and a width-7 NAF with a precomputed table for the base point, joined
by Shamir's trick (the approach of `curve25519-dalek`'s
`vartime_double_scalar_mul_basepoint`).
-/

namespace NearCrypto.Ed25519

open Field

/-- A point in extended coordinates. -/
structure Ext where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
  deriving Inhabited

namespace Ext

/-- The identity. -/
def identity : Ext :=
  ⟨0, 1, 1, 0⟩

/-- The negative of a point. -/
def neg (P : Ext) : Ext :=
  ⟨2 * p - P.x, P.y, P.z, 2 * p - P.t⟩

/-- Addition. -/
def add (P Q : Ext) : Ext :=
  let a := mul (P.y + 2 * p - P.x) (Q.y + 2 * p - Q.x)
  let b := mul (P.y + P.x) (Q.y + Q.x)
  let c := mul (mul P.t d2) Q.t
  let d := mul (2 * P.z) Q.z
  let e := b + p - a
  let f := d + p - c
  let g := d + c
  let h := b + a
  ⟨mul e f, mul g h, mul f g, mul e h⟩

/-- Doubling. -/
def dbl (P : Ext) : Ext :=
  let a := sq P.x
  let b := sq P.y
  let c := 2 * sq P.z
  let e := sq (P.x + P.y) + 2 * p - a - b
  let g := b + p - a
  let f := g + 2 * p - c
  let h := 2 * p - a - b
  ⟨mul e f, mul g h, mul f g, mul e h⟩

/-- Subtraction. -/
def sub (P Q : Ext) : Ext :=
  add P (neg Q)

/-- Lift an affine point. -/
def ofAffine (x y : Nat) : Ext :=
  ⟨x, y, 1, mul x y⟩

/-- The base point `(x, 4/5)` with `x` even. -/
def basePoint : Ext :=
  ofAffine 15112221349535400772501151409588531511454012693041857206046113283949847762202
    46316835694926478169428394003475163141307993866256225615783033603165251855960

/-- The canonical 32-byte encoding. -/
def compress (P : Ext) : ByteArray :=
  let zi := inv P.z
  let x := mul P.x zi
  let y := mul P.y zi
  Scalar.toBytes32 (y ||| (x &&& 1) <<< 255)

/-- `curve25519-dalek`'s `CompressedEdwardsY::decompress`; see the notes in `Spec`. -/
def decompress (b : ByteArray) : Option Ext :=
  if b.size != 32 then none
  else
    let n := Scalar.ofBytes b 0 4
    let y := n % 2 ^ 255 % p
    let yy := sq y
    match sqrtRatio (yy + p - 1) (mul yy d + 1) with
    | none => none
    | some x =>
      let x := x % p
      let x := if x &&& 1 = 1 then p - x else x
      let x := if n >>> 255 = 1 then (p - x) % p else x
      some (ofAffine x y)

/-- The odd multiples `P, 3P, …, (2 n - 1) P`. -/
def oddMultiples (P : Ext) (n : Nat) : Array Ext :=
  let P2 := dbl P
  (List.range (n - 1)).foldl (fun (t : Array Ext) _ => t.push (add t.back! P2)) #[P]

/-- The width-`w` non-adjacent form of `k`, least significant digit first. -/
def naf (w : Nat) (k : Nat) : Array Int :=
  let rec go : Nat → Nat → Array Int → Array Int
    | 0, _, acc => acc
    | fuel + 1, k, acc =>
      if k = 0 then acc
      else
        if k % 2 = 0 then go fuel (k / 2) (acc.push 0)
        else
          let m : Int := (k % 2 ^ w : Nat)
          let dg : Int := if m ≥ 2 ^ (w - 1) then m - 2 ^ w else m
          go fuel (((k : Int) - dg).toNat / 2) (acc.push dg)
  go 260 k #[]

/-- Add `digit · P` for the odd `digit` using the table of odd multiples. -/
@[inline]
def addDigit (R : Ext) (table : Array Ext) (digit : Int) : Ext :=
  if digit > 0 then add R table[(digit.toNat - 1) / 2]!
  else if digit < 0 then sub R table[((-digit).toNat - 1) / 2]! else R

/-- Odd multiples of the base point up to 63 (width-7 NAF digits). -/
def baseTable : Array Ext :=
  oddMultiples basePoint 32

/-- Shamir's trick: from the top digit down, `R = 2 R + a_i A + b_i B`. -/
private def shamir (nafA nafB : Array Int) (tableA : Array Ext) : Nat → Ext → Ext
  | 0, R => R
  | i + 1, R =>
    let R := dbl R
    let R := addDigit R tableA nafA[i]!
    shamir nafA nafB tableA i (addDigit R baseTable nafB[i]!)

/-- `a · A + b · B` for the base point `B`, in variable time. -/
def doubleMulBase (a : Nat) (A : Ext) (b : Nat) : Ext :=
  let nafA := naf 5 a
  let nafB := naf 7 b
  let n := max nafA.size nafB.size
  shamir (nafA ++ Array.replicate (n - nafA.size) 0) (nafB ++ Array.replicate (n - nafB.size) 0)
    (oddMultiples A 8) n identity

/-- `b · B`. -/
def mulBase (b : Nat) : Ext :=
  let nafB := naf 7 b
  (List.range nafB.size).reverse.foldl (fun R i => addDigit (dbl R) baseTable nafB[i]!) identity

end Ext

end NearCrypto.Ed25519
