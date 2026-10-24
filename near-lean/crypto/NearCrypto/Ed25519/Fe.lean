import NearCrypto.Ed25519.Scalar

/-!
# GF(2²⁵⁵ − 19) in ten limbs

A field element is ten `UInt64` limbs in radix 2^25.5: limb `i` has weight `2^⌈25.5 i⌉`, so the
limbs have 26 and 25 bits alternately (as in ref10 and curve25519-donna-32bit). The limbs of the
result of `mul`, `sq`, `add` and `sub` are *reduced*: below `2²⁶` (the second below `2²⁵ + 2¹⁶`).
Products of limbs below `2²⁷` leave every accumulator of `mul` below `2⁶³`, so wrapping `UInt64`
arithmetic is exact; the operands of `mul` and `sq` may therefore be sums of two reduced elements,
and `sub` needs its second operand reduced. A value is only canonical (below `p`) after `toNat`.

A `Nat` product followed by `%` costs about 280 ns, the limb product about 55 ns, which is the
reason for this representation (design notes, M2). Nothing here is constant time.
-/

namespace NearCrypto.Ed25519

/-- Ten limbs of widths 26, 25, 26, 25, ... -/
structure Fe where
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

namespace Fe

/-- Propagate carries and wrap the top carry with `2²⁵⁵ = 19`; inputs below `2⁶³`. -/
@[inline]
def carry (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : UInt64) : Fe :=
  let c := r0 >>> 26
  let r0 := r0 &&& 0x3ffffff
  let r1 := r1 + c
  let c := r1 >>> 25
  let r1 := r1 &&& 0x1ffffff
  let r2 := r2 + c
  let c := r2 >>> 26
  let r2 := r2 &&& 0x3ffffff
  let r3 := r3 + c
  let c := r3 >>> 25
  let r3 := r3 &&& 0x1ffffff
  let r4 := r4 + c
  let c := r4 >>> 26
  let r4 := r4 &&& 0x3ffffff
  let r5 := r5 + c
  let c := r5 >>> 25
  let r5 := r5 &&& 0x1ffffff
  let r6 := r6 + c
  let c := r6 >>> 26
  let r6 := r6 &&& 0x3ffffff
  let r7 := r7 + c
  let c := r7 >>> 25
  let r7 := r7 &&& 0x1ffffff
  let r8 := r8 + c
  let c := r8 >>> 26
  let r8 := r8 &&& 0x3ffffff
  let r9 := r9 + c
  let c := r9 >>> 25
  let r9 := r9 &&& 0x1ffffff
  let r0 := r0 + 19 * c
  let c := r0 >>> 26
  let r0 := r0 &&& 0x3ffffff
  ⟨r0, r1 + c, r2, r3, r4, r5, r6, r7, r8, r9⟩

/-- Zero. -/
def zero : Fe :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- One. -/
def one : Fe :=
  ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The element with value `n` (`n < 2²⁵⁵`; it need not be below `p`). -/
def ofNat (n : Nat) : Fe :=
  ⟨(n &&& 0x3ffffff).toUInt64, (n >>> 26 &&& 0x1ffffff).toUInt64, (n >>> 51 &&& 0x3ffffff).toUInt64,
    (n >>> 77 &&& 0x1ffffff).toUInt64, (n >>> 102 &&& 0x3ffffff).toUInt64,
    (n >>> 128 &&& 0x1ffffff).toUInt64, (n >>> 153 &&& 0x3ffffff).toUInt64,
    (n >>> 179 &&& 0x1ffffff).toUInt64, (n >>> 204 &&& 0x3ffffff).toUInt64,
    (n >>> 230 &&& 0x1ffffff).toUInt64⟩

/-- The canonical value, below `p`. -/
def toNat (a : Fe) : Nat :=
  (a.l0.toNat + a.l1.toNat <<< 26 + a.l2.toNat <<< 51 + a.l3.toNat <<< 77 + a.l4.toNat <<< 102 +
      a.l5.toNat <<< 128 +
      a.l6.toNat <<< 153 +
      a.l7.toNat <<< 179 +
      a.l8.toNat <<< 204 +
      a.l9.toNat <<< 230) %
    p

/-- Equality of values. -/
def eq (a b : Fe) : Bool :=
  a.toNat == b.toNat

/-- Sum. -/
def add (a b : Fe) : Fe :=
  carry (a.l0 + b.l0) (a.l1 + b.l1) (a.l2 + b.l2) (a.l3 + b.l3) (a.l4 + b.l4) (a.l5 + b.l5)
    (a.l6 + b.l6) (a.l7 + b.l7) (a.l8 + b.l8) (a.l9 + b.l9)

/-- Difference, as `a + 2 p - b` limb by limb (`b` reduced, so no limb underflows). -/
def sub (a b : Fe) : Fe :=
  carry (a.l0 + 0x7ffffda - b.l0) (a.l1 + 0x3fffffe - b.l1) (a.l2 + 0x7fffffe - b.l2)
    (a.l3 + 0x3fffffe - b.l3) (a.l4 + 0x7fffffe - b.l4) (a.l5 + 0x3fffffe - b.l5)
    (a.l6 + 0x7fffffe - b.l6) (a.l7 + 0x3fffffe - b.l7) (a.l8 + 0x7fffffe - b.l8)
    (a.l9 + 0x3fffffe - b.l9)

/-- Negation. -/
def neg (a : Fe) : Fe :=
  sub zero a

end Fe

end NearCrypto.Ed25519
