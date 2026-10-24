import NearCrypto.Ed25519.FeMul

/-!
# edwards25519 in extended coordinates

Points are `(X : Y : Z : T)` with `x = X/Z`, `y = Y/Z` and `T = X Y / Z`. The formulas are
`add-2008-hwcd-3` and `dbl-2008-hwcd` for `a = −1`; both are complete on this curve. Table entries
are kept as `Cached` points `(Y + X, Y − X, Z, 2 d T)`, which saves a product per addition.
Scalar multiplication is a width-5 NAF for variable points and a width-7 NAF over a precomputed
table for the base point, joined by Shamir's trick (the approach of `curve25519-dalek`'s
`vartime_double_scalar_mul_basepoint`), in variable time.
-/

namespace NearCrypto.Ed25519

namespace Fe

/-- A square root of `−1`. -/
def sqrtM1 : Fe :=
  ofNat 19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- The curve constant `d = −121665 / 121666`. -/
def d : Fe :=
  ofNat 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `2 d`. -/
def d2 : Fe :=
  add d d

/-- `a ^ (2 ^ k)`. -/
def pow2k (a : Fe) : Nat → Fe
  | 0 => a
  | k + 1 => pow2k (sq a) k

/-- `(a ^ (2 ^ 250 - 1), a ^ 11)`: the common prefix of the inversion and square-root chains. -/
def pow250 (a : Fe) : Fe × Fe :=
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
def inv (a : Fe) : Fe :=
  let (z250, z11) := pow250 a
  mul (pow2k z250 5) z11

/-- `a ^ ((p - 5) / 8) = a ^ (2 ^ 252 - 3)`. -/
def powP58 (a : Fe) : Fe :=
  mul (pow2k (pow250 a).1 2) a

/-- A root of `u / v` when there is one (the `sqrt_ratio_i` of `curve25519-dalek`, up to the sign
of the root). -/
def sqrtRatio (u v : Fe) : Option Fe :=
  let v3 := mul (sq v) v
  let v7 := mul (sq v3) v
  let r := mul (mul u v3) (powP58 (mul u v7))
  let c := mul v (sq r)
  if c.eq u then some r else if c.eq (neg u) then some (mul r sqrtM1) else none

end Fe

open Fe

/-- A point in extended coordinates. -/
structure Ext where
  x : Fe
  y : Fe
  z : Fe
  t : Fe
  deriving Inhabited

/-- A point as `(Y + X, Y − X, Z, 2 d T)`, the right operand of an addition. -/
structure Cached where
  ypx : Fe
  ymx : Fe
  z : Fe
  t2d : Fe
  deriving Inhabited

namespace Ext

/-- The identity. -/
def identity : Ext :=
  ⟨zero, one, one, zero⟩

/-- The negative of a point. -/
def neg (P : Ext) : Ext :=
  ⟨Fe.neg P.x, P.y, P.z, Fe.neg P.t⟩

/-- Lift an affine point. -/
def ofAffine (x y : Fe) : Ext :=
  ⟨x, y, one, mul x y⟩

/-- The base point `(x, 4/5)` with `x` even. -/
def basePoint : Ext :=
  ofAffine (Fe.ofNat 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (Fe.ofNat 46316835694926478169428394003475163141307993866256225615783033603165251855960)

/-- The cached form. -/
def toCached (P : Ext) : Cached :=
  ⟨add P.y P.x, sub P.y P.x, P.z, mul P.t d2⟩

/-- `P + Q`. -/
def addCached (P : Ext) (Q : Cached) : Ext :=
  let a := mul (sub P.y P.x) Q.ymx
  let b := mul (add P.y P.x) Q.ypx
  let c := mul P.t Q.t2d
  let d := mul (add P.z P.z) Q.z
  let e := sub b a
  let f := sub d c
  let g := add d c
  let h := add b a
  ⟨mul e f, mul g h, mul f g, mul e h⟩

/-- `P - Q`: the sum with `Q` negated, which swaps `Y + X` and `Y - X` and the sign of `2 d T`. -/
def subCached (P : Ext) (Q : Cached) : Ext :=
  let a := mul (sub P.y P.x) Q.ypx
  let b := mul (add P.y P.x) Q.ymx
  let c := mul P.t Q.t2d
  let d := mul (add P.z P.z) Q.z
  let e := sub b a
  let f := add d c
  let g := sub d c
  let h := add b a
  ⟨mul e f, mul g h, mul f g, mul e h⟩

/-- `P + Q`. -/
def add (P Q : Ext) : Ext :=
  addCached P Q.toCached

/-- Doubling; the `T` coordinate of the result (needed by a following addition, and by whoever
uses the point) is only computed when `needT`. -/
def dbl (P : Ext) (needT : Bool := true) : Ext :=
  let a := sq P.x
  let b := sq P.y
  let c := Fe.add (sq P.z) (sq P.z)
  let e := sub (sub (sq (Fe.add P.x P.y)) a) b
  let g := sub b a
  let f := sub g c
  let h := sub (sub zero a) b
  ⟨mul e f, mul g h, mul f g, if needT then mul e h else zero⟩

/-- The canonical 32-byte encoding. -/
def compress (P : Ext) : ByteArray :=
  let zi := inv P.z
  let x := (mul P.x zi).toNat
  let y := (mul P.y zi).toNat
  Scalar.toBytes32 (y ||| (x &&& 1) <<< 255)

/-- `curve25519-dalek`'s `CompressedEdwardsY::decompress`; see the notes in `Spec`. -/
def decompress (b : ByteArray) : Option Ext :=
  if b.size != 32 then none
  else
    let n := Scalar.ofBytes b 0 4
    let y := Fe.ofNat (n % 2 ^ 255)
    let yy := sq y
    match sqrtRatio (sub yy one) (Fe.add (mul yy d) one) with
    | none => none
    | some x =>
      let x := x.toNat
      let x := if x &&& 1 = 1 then p - x else x
      let x := if n >>> 255 = 1 then (p - x) % p else x
      some (ofAffine (Fe.ofNat x) y)

/-- The odd multiples `P, 3P, …, (2 n - 1) P`. -/
def oddMultiples (P : Ext) (n : Nat) : Array Cached :=
  let P2 := (dbl P).toCached
  let rec go : Nat → Ext → Array Cached → Array Cached
    | 0, _, t => t
    | k + 1, last, t =>
      let next := addCached last P2
      go k next (t.push next.toCached)
  go (n - 1) P #[P.toCached]

/-- The width-`w` non-adjacent form of `k < 2²⁵⁵`: 256 digits, least significant first, each zero
or odd with absolute value below `2 ^ (w - 1)`. -/
def naf (w : Nat) (k : Nat) : Array Int :=
  let words : Array UInt64 :=
    #[k.toUInt64, (k >>> 64).toUInt64, (k >>> 128).toUInt64, (k >>> 192).toUInt64, 0]
  let width : UInt64 := 1 <<< w.toUInt64
  let mask := width - 1
  let rec go : Nat → Nat → UInt64 → Array Int → Array Int
    | 0, _, _, digits => digits
    | fuel + 1, pos, carry, digits =>
      if pos ≥ 256 then digits
      else
        let idx := pos / 64
        let bit := (pos % 64).toUInt64
        let buf :=
          if pos % 64 < 64 - w then words[idx]! >>> bit
          else words[idx]! >>> bit ||| words[idx + 1]! <<< (64 - bit)
        let window := carry + (buf &&& mask)
        if window &&& 1 == 0 then go fuel (pos + 1) carry digits
        else
          if window < width / 2 then go fuel (pos + w) 0 (digits.set! pos (Int.ofNat window.toNat))
          else
            go fuel (pos + w) 1 (digits.set! pos (Int.ofNat window.toNat - Int.ofNat width.toNat))
  go 256 0 0 (Array.replicate 256 0)

/-- Add `digit · P` for the odd `digit` using the table of odd multiples. -/
@[inline]
def addDigit (R : Ext) (table : Array Cached) (digit : Int) : Ext :=
  if digit > 0 then addCached R table[(digit.toNat - 1) / 2]!
  else if digit < 0 then subCached R table[((-digit).toNat - 1) / 2]! else R

/-- Odd multiples of the base point up to 63 (width-7 NAF digits). -/
def baseTable : Array Cached :=
  oddMultiples basePoint 32

/-- Shamir's trick from digit `i - 1` down: `R = 2 R + a_j A + b_j B`. -/
private def shamir (nafA nafB : Array Int) (tableA : Array Cached) : Nat → Ext → Ext
  | 0, R => R
  | i + 1, R =>
    let da := nafA[i]!
    let db := nafB[i]!
    let R := dbl R (i == 0 || da != 0 || db != 0)
    let R := addDigit R tableA da
    shamir nafA nafB tableA i (addDigit R baseTable db)

/-- `a · A + b · B` for the base point `B` (`a`, `b < 2²⁵⁵`), in variable time. -/
def doubleMulBase (a : Nat) (A : Ext) (b : Nat) : Ext :=
  let nafA := naf 5 a
  let nafB := naf 7 b
  let top := ((List.range 256).reverse.find? fun i => nafA[i]! != 0 || nafB[i]! != 0).getD 0
  shamir nafA nafB (oddMultiples A 8) (top + 1) identity

/-- `b · B` (`b < 2²⁵⁵`). -/
def mulBase (b : Nat) : Ext :=
  let nafB := naf 7 b
  let rec go : Nat → Ext → Ext
    | 0, R => R
    | i + 1, R =>
      let db := nafB[i]!
      go i (addDigit (dbl R (i == 0 || db != 0)) baseTable db)
  go 256 identity

end Ext

end NearCrypto.Ed25519
