import NearCrypto.Bytes

/-!
# GF(2²⁵⁶ − 2³² − 977) in ten limbs

A field element is ten `UInt64` limbs of radix 2²⁶: limb `i` has weight `2^(26 i)`, so the top
limb holds bits 234 to 259 and a reduced element has it below `2²²`. The limbs of the result of
`mul`, `sq`, `add`, `sub` and `mulInt` are *reduced*: below `2²⁶` (the third below `2²⁶ + 2²¹`)
and the top one below `2²²`. Products of limbs below `2²⁸` leave every column of `mul` below
`2⁶¹`, so wrapping `UInt64` arithmetic is exact; the operands of `mul` and `sq` may therefore be
sums of a few reduced elements, and `sub` needs its second operand reduced. A value is only
canonical (below `p`) after `toNat`. `2²⁵⁶ ≡ 2³² + 977`, which `carry` uses to wrap the top.

Nothing here is constant time.
-/

namespace NearCrypto.Secp256k1

/-- The field prime. -/
def p : Nat :=
  2 ^ 256 - 2 ^ 32 - 977

/-- The group order. -/
def n : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- Ten limbs of 26 bits. -/
structure Fp where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  l9 : UInt64
  deriving Inhabited

namespace Fp

/-- Propagate carries and wrap bits 256 and up with `2²⁵⁶ = 2³² + 977`; inputs below `2⁶²`. -/
@[inline]
def carry (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : UInt64) : Fp :=
  let c := r0 >>> 26
  let r0 := r0 &&& 0x3ffffff
  let r1 := r1 + c
  let c := r1 >>> 26
  let r1 := r1 &&& 0x3ffffff
  let r2 := r2 + c
  let c := r2 >>> 26
  let r2 := r2 &&& 0x3ffffff
  let r3 := r3 + c
  let c := r3 >>> 26
  let r3 := r3 &&& 0x3ffffff
  let r4 := r4 + c
  let c := r4 >>> 26
  let r4 := r4 &&& 0x3ffffff
  let r5 := r5 + c
  let c := r5 >>> 26
  let r5 := r5 &&& 0x3ffffff
  let r6 := r6 + c
  let c := r6 >>> 26
  let r6 := r6 &&& 0x3ffffff
  let r7 := r7 + c
  let c := r7 >>> 26
  let r7 := r7 &&& 0x3ffffff
  let r8 := r8 + c
  let c := r8 >>> 26
  let r8 := r8 &&& 0x3ffffff
  let r9 := r9 + c
  let c := r9 >>> 22
  let r9 := r9 &&& 0x3fffff
  let r0 := r0 + 977 * c
  let r1 := r1 + (c <<< 6)
  let c := r0 >>> 26
  let r0 := r0 &&& 0x3ffffff
  let r1 := r1 + c
  let c := r1 >>> 26
  ⟨r0, r1 &&& 0x3ffffff, r2 + c, r3, r4, r5, r6, r7, r8, r9⟩

/-- Zero. -/
def zero : Fp :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- One. -/
def one : Fp :=
  ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The element with value `x` (`x < 2²⁶⁰`; it need not be below `p`). -/
def ofNat (x : Nat) : Fp :=
  ⟨(x &&& 0x3ffffff).toUInt64, (x >>> 26 &&& 0x3ffffff).toUInt64, (x >>> 52 &&& 0x3ffffff).toUInt64,
    (x >>> 78 &&& 0x3ffffff).toUInt64, (x >>> 104 &&& 0x3ffffff).toUInt64,
    (x >>> 130 &&& 0x3ffffff).toUInt64, (x >>> 156 &&& 0x3ffffff).toUInt64,
    (x >>> 182 &&& 0x3ffffff).toUInt64, (x >>> 208 &&& 0x3ffffff).toUInt64,
    (x >>> 234 &&& 0x3ffffff).toUInt64⟩

/-- The value, not reduced. -/
def value (a : Fp) : Nat :=
  a.l0.toNat + a.l1.toNat <<< 26 + a.l2.toNat <<< 52 + a.l3.toNat <<< 78 + a.l4.toNat <<< 104 +
    a.l5.toNat <<< 130 +
    a.l6.toNat <<< 156 +
    a.l7.toNat <<< 182 +
    a.l8.toNat <<< 208 +
    a.l9.toNat <<< 234

/-- The canonical value, below `p`. -/
def toNat (a : Fp) : Nat :=
  a.value % p

/-- Sum. -/
def add (a b : Fp) : Fp :=
  carry (a.l0 + b.l0) (a.l1 + b.l1) (a.l2 + b.l2) (a.l3 + b.l3) (a.l4 + b.l4) (a.l5 + b.l5)
    (a.l6 + b.l6) (a.l7 + b.l7) (a.l8 + b.l8) (a.l9 + b.l9)

/-- Difference, as `a + 2 p - b` limb by limb (`b` reduced, so no limb underflows). -/
def sub (a b : Fp) : Fp :=
  carry (a.l0 + 0x7fff85e - b.l0) (a.l1 + 0x7ffff7e - b.l1) (a.l2 + 0x7fffffe - b.l2)
    (a.l3 + 0x7fffffe - b.l3) (a.l4 + 0x7fffffe - b.l4) (a.l5 + 0x7fffffe - b.l5)
    (a.l6 + 0x7fffffe - b.l6) (a.l7 + 0x7fffffe - b.l7) (a.l8 + 0x7fffffe - b.l8)
    (a.l9 + 0x7ffffe - b.l9)

/-- Negation. -/
def neg (a : Fp) : Fp :=
  sub zero a

/-- Product with a small constant `k < 2²⁰`. -/
def mulInt (a : Fp) (k : UInt64) : Fp :=
  carry (a.l0 * k) (a.l1 * k) (a.l2 * k) (a.l3 * k) (a.l4 * k) (a.l5 * k) (a.l6 * k) (a.l7 * k)
    (a.l8 * k) (a.l9 * k)

/-- Whether the value is `0` modulo `p`: after a full carry the value is below `2p`, so it is
`0` or `p`. -/
def isZero (a : Fp) : Bool :=
  let c := a.l0 >>> 26
  let t0 := a.l0 &&& 0x3ffffff
  let x := a.l1 + c
  let c := x >>> 26
  let t1 := x &&& 0x3ffffff
  let x := a.l2 + c
  let c := x >>> 26
  let t2 := x &&& 0x3ffffff
  let x := a.l3 + c
  let c := x >>> 26
  let t3 := x &&& 0x3ffffff
  let x := a.l4 + c
  let c := x >>> 26
  let t4 := x &&& 0x3ffffff
  let x := a.l5 + c
  let c := x >>> 26
  let t5 := x &&& 0x3ffffff
  let x := a.l6 + c
  let c := x >>> 26
  let t6 := x &&& 0x3ffffff
  let x := a.l7 + c
  let c := x >>> 26
  let t7 := x &&& 0x3ffffff
  let x := a.l8 + c
  let c := x >>> 26
  let t8 := x &&& 0x3ffffff
  let t9 := a.l9 + c
  let rest := t1 ||| t2 ||| t3 ||| t4 ||| t5 ||| t6 ||| t7 ||| t8
  (t0 == 0 && rest == 0 && t9 == 0) ||
    (t0 == 0x3fffc2f && t1 == 0x3ffffbf &&
      t2 &&& t3 &&& t4 &&& t5 &&& t6 &&& t7 &&& t8 == 0x3ffffff &&
      t9 == 0x3fffff)

/-- Equality of values. -/
def eq (a b : Fp) : Bool :=
  isZero (sub a b)

/-- The 32 big-endian bytes of the canonical value. -/
def toBytes (a : Fp) : ByteArray :=
  let x := a.toNat
  pushBe64
    (pushBe64 (pushBe64 (pushBe64 ByteArray.empty (x >>> 192).toUInt64) (x >>> 128).toUInt64)
      (x >>> 64).toUInt64)
    x.toUInt64

end Fp

end NearCrypto.Secp256k1
