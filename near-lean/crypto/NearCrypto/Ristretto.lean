import NearCrypto.Ed25519.Curve
import NearCrypto.Ed25519.Spec

/-!
# ristretto255

The prime-order group of RFC 9496 on top of edwards25519, as `curve25519-dalek` 4.1.3 implements
it (`ristretto.rs`: `CompressedRistretto::decompress` and `RistrettoPoint::compress`, and
`field.rs`: `sqrt_ratio_i`). A ristretto point is represented by any point of the coset of
the 4-torsion in the Edwards group, so the group law is the Edwards one; only the encodings
differ. Decoding accepts exactly the canonical, even `s` whose point has an Edwards representative
with an even `t` and a nonzero `y`:

* the 32 bytes read little-endian must be below `p` (bit 255 set is therefore rejected) and even;
* `v (1 + s²)²` with `v = -d (1 - s²)² - (1 + s²)²` must be a nonzero square (`was_square` of
  `sqrt_ratio_i(1, v (1 + s²)²)`), and the point `(x, y)` it yields must have `t = x y` even and `y`
  nonzero.

`Spec` follows the RFC over `Nat`; `Impl` uses the ten-limb field and the extended points of
`Ed25519`.
-/

namespace NearCrypto.Ristretto

/-! ### Spec -/

namespace Spec

open Ed25519.Spec

/-- Whether the field element is odd (`IS_NEGATIVE`). -/
def isNegative (x : Nat) : Bool :=
  x % p % 2 == 1

/-- The even representative (`CT_ABS`). -/
def abs (x : Nat) : Nat :=
  if isNegative x then (p - x % p) % p else x % p

/-- RFC 9496 `SQRT_RATIO_M1`: whether `u / v` is a square, and the nonnegative square root of
`u / v` (of `i u / v` when it is not). -/
def sqrtRatio (u v : Nat) : Bool × Nat :=
  let u := u % p
  let v := v % p
  let v3 := v * v % p * v % p
  let v7 := v3 * v3 % p * v % p
  let r := u * v3 % p * powMod (u * v7 % p) ((p - 5) / 8) % p
  let check := v * r % p * r % p
  let negU := (p - u) % p
  let correct := check == u
  let flipped := check == negU
  let flippedI := check == negU * sqrtM1 % p
  let r := if flipped || flippedI then r * sqrtM1 % p else r
  (correct || flipped, abs r)

/-- `1 / sqrt(a - d)` with `a = -1`. -/
def invSqrtAMinusD : Nat :=
  (sqrtRatio 1 ((p - 1 + p - d) % p)).2

/-- RFC 9496 decoding: the affine `(x, y)` with `t = x y`. -/
def decode (b : ByteArray) : Option (Nat × Nat) :=
  let s := toNat b
  if b.size != 32 || s ≥ p || isNegative s then none
  else
    let ss := s * s % p
    let u1 := (1 + p - ss) % p
    let u2 := (1 + ss) % p
    let u2sq := u2 * u2 % p
    let v := (p - d * (u1 * u1 % p) % p + p - u2sq) % p
    let (ok, invsqrt) := sqrtRatio 1 (v * u2sq % p)
    let denX := invsqrt * u2 % p
    let denY := invsqrt * denX % p * v % p
    let x := abs (2 * s % p * denX % p)
    let y := u1 * denY % p
    if !ok || isNegative (x * y % p) || y == 0 then none else some (x, y)

/-- `curve25519-dalek` `CompressedRistretto::decompress`, as an Edwards point. -/
def decompress (b : ByteArray) : Option Point :=
  (decode b).map fun (x, y) => (x, y, 1)

/-- RFC 9496 encoding of an Edwards point. -/
def compress (P : Point) : ByteArray :=
  let zi := inv P.2.2
  let x0 := P.1 * zi % p
  let y0 := P.2.1 * zi % p
  let z0 := 1
  let t0 := x0 * y0 % p
  let u1 := (z0 + y0) * (z0 + p - y0) % p
  let u2 := x0 * y0 % p
  let (_, invsqrt) := sqrtRatio 1 (u1 * (u2 * u2 % p) % p)
  let den1 := invsqrt * u1 % p
  let den2 := invsqrt * u2 % p
  let zInv := den1 * den2 % p * t0 % p
  let ix0 := x0 * sqrtM1 % p
  let iy0 := y0 * sqrtM1 % p
  let enchanted := den1 * invSqrtAMinusD % p
  let rotate := isNegative (t0 * zInv % p)
  let x := if rotate then iy0 else x0
  let y := if rotate then ix0 else y0
  let denInv := if rotate then enchanted else den2
  let y := if isNegative (x * zInv % p) then (p - y) % p else y
  ofNat 32 (abs (denInv * ((z0 + p - y) % p) % p))

end Spec

/-! ### Impl -/

namespace Impl

open Ed25519 Ed25519.Fe

/-- Whether the field element is odd (`IS_NEGATIVE`). -/
def isNegative (a : Fe) : Bool :=
  a.toNat % 2 == 1

/-- The even representative (`CT_ABS`). -/
def abs (a : Fe) : Fe :=
  if isNegative a then Fe.neg a else a

/-- `sqrt_ratio_i` of `curve25519-dalek`; see `Spec.sqrtRatio`. -/
def sqrtRatio (u v : Fe) : Bool × Fe :=
  let v3 := mul (sq v) v
  let v7 := mul (sq v3) v
  let r := mul (mul u v3) (powP58 (mul u v7))
  let check := mul v (sq r)
  let negU := Fe.neg u
  let correct := check.eq u
  let flipped := check.eq negU
  let flippedI := check.eq (mul negU sqrtM1)
  let r := if flipped || flippedI then mul r sqrtM1 else r
  (correct || flipped, abs r)

/-- `1 / sqrt(a - d)` with `a = -1`. -/
def invSqrtAMinusD : Fe :=
  (sqrtRatio one (Fe.neg (Fe.add one d))).2

/-- `CompressedRistretto::decompress`: an Edwards point of the coset. -/
def decompress (b : ByteArray) : Option Ext :=
  if b.size != 32 then none
  else
    let n := Scalar.ofBytes b 0 4
    if n ≥ p || n % 2 == 1 then none
    else
      let s := Fe.ofNat n
      let ss := sq s
      let u1 := sub one ss
      let u2 := Fe.add one ss
      let u2sq := sq u2
      let v := sub (Fe.neg (mul d (sq u1))) u2sq
      let (ok, invsqrt) := sqrtRatio one (mul v u2sq)
      let denX := mul invsqrt u2
      let denY := mul invsqrt (mul denX v)
      let x := abs (mul (Fe.add s s) denX)
      let y := mul u1 denY
      let t := mul x y
      if !ok || isNegative t || y.toNat == 0 then none else some ⟨x, y, one, t⟩

/-- `RistrettoPoint::compress`. -/
def compress (P : Ext) : ByteArray :=
  let u1 := mul (Fe.add P.z P.y) (sub P.z P.y)
  let u2 := mul P.x P.y
  let (_, invsqrt) := sqrtRatio one (mul u1 (sq u2))
  let den1 := mul invsqrt u1
  let den2 := mul invsqrt u2
  let zInv := mul (mul den1 den2) P.t
  let ix0 := mul P.x sqrtM1
  let iy0 := mul P.y sqrtM1
  let enchanted := mul den1 invSqrtAMinusD
  let rotate := isNegative (mul P.t zInv)
  let x := if rotate then iy0 else P.x
  let y := if rotate then ix0 else P.y
  let denInv := if rotate then enchanted else den2
  let y := if isNegative (mul x zInv) then Fe.neg y else y
  Scalar.toBytes32 (abs (mul denInv (sub P.z y))).toNat

end Impl

end NearCrypto.Ristretto
