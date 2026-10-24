import NearCrypto.Pairing.Nat

/-!
# The quadratic extension `Fp[u] / (u² + 1)`

BN254 and BLS12-381 both have `p ≡ 3 (mod 4)`, so `-1` is a non-residue and the quadratic extension
is `Fp[u] / (u² + 1)`; `a + b u` is `⟨a, b⟩` with `a, b < p`. Every function takes the prime first
and expects reduced arguments.
-/

namespace NearCrypto.Pairing

/-- `c0 + c1 u`. -/
structure Fp2 where
  c0 : Nat
  c1 : Nat
  deriving BEq, Inhabited

namespace Fp2

def zero : Fp2 :=
  ⟨0, 0⟩

def one : Fp2 :=
  ⟨1, 0⟩

def isZero (a : Fp2) : Bool :=
  a.c0 == 0 && a.c1 == 0

/-- `a + b mod p` for reduced arguments, by a conditional subtraction. -/
@[inline]
def addMod (p a b : Nat) : Nat :=
  let s := a + b
  if s ≥ p then s - p else s

/-- `a - b mod p` for reduced arguments. -/
@[inline]
def subMod (p a b : Nat) : Nat :=
  if a ≥ b then a - b else a + p - b

def add (p : Nat) (a b : Fp2) : Fp2 :=
  ⟨addMod p a.c0 b.c0, addMod p a.c1 b.c1⟩

def sub (p : Nat) (a b : Fp2) : Fp2 :=
  ⟨subMod p a.c0 b.c0, subMod p a.c1 b.c1⟩

def neg (p : Nat) (a : Fp2) : Fp2 :=
  ⟨subMod p 0 a.c0, subMod p 0 a.c1⟩

/-- Product: three multiplications and two reductions (Karatsuba). -/
def mul (p : Nat) (a b : Fp2) : Fp2 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  ⟨if t0 ≥ t1 then (t0 - t1) % p else (p - (t1 - t0) % p) % p,
    ((a.c0 + a.c1) * (b.c0 + b.c1) - t0 - t1) % p⟩

/-- Square: `(a₀ + a₁)(a₀ - a₁) + 2 a₀ a₁ u`. -/
def sqr (p : Nat) (a : Fp2) : Fp2 :=
  ⟨(a.c0 + a.c1) * (a.c0 + p - a.c1) % p, 2 * a.c0 * a.c1 % p⟩

/-- Multiplication by an element of `Fp`. -/
def scale (p : Nat) (a : Fp2) (k : Nat) : Fp2 :=
  ⟨a.c0 * k % p, a.c1 * k % p⟩

def conj (p : Nat) (a : Fp2) : Fp2 :=
  ⟨a.c0, (p - a.c1) % p⟩

/-- The inverse, through the norm `a₀² + a₁²`; zero for zero. -/
def inv (p : Nat) (a : Fp2) : Fp2 :=
  let n := invMod p ((a.c0 * a.c0 + a.c1 * a.c1) % p)
  ⟨a.c0 * n % p, (p - a.c1) * n % p⟩

/-- `a ^ e`. -/
def pow (p : Nat) (a : Fp2) (e : Nat) : Fp2 :=
  Id.run do
    let mut r := one
    let mut b := a
    for i in [0:e.log2 + 1] do
      if e.testBit i then
        r := mul p r b
      b := sqr p b
    return r

/-- Whether `a` is a square in `Fp2`: exactly when its norm is a square in `Fp`. -/
def isSquare (p : Nat) (a : Fp2) : Bool :=
  isSquareMod p ((a.c0 * a.c0 + a.c1 * a.c1) % p)

/-- A square root of `a`, when there is one (any of the two). -/
def sqrt (p : Nat) (a : Fp2) : Option Fp2 :=
  let root : Option Fp2 :=
    if a.c1 == 0 then
      match sqrtMod p a.c0 with
      | some r => some ⟨r, 0⟩
      | none => (sqrtMod p ((p - a.c0) % p)).map fun r => ⟨0, r⟩
    else
      match sqrtMod p ((a.c0 * a.c0 + a.c1 * a.c1) % p) with
      | none => none
      | some s =>
        let half := (p + 1) / 2
        let t := (a.c0 + s) * half % p
        let t := if isSquareMod p t then t else (a.c0 + (p - s)) * half % p
        (sqrtMod p t).map fun x => ⟨x, a.c1 * invMod p (2 * x % p) % p⟩
  root.filter fun r => sqr p r == a

/-- The sign of an element for hash-to-curve (`sgn0`, RFC 9380 section 4.1, `m = 2`). -/
def sgn0 (a : Fp2) : Bool :=
  a.c0 % 2 == 1 || (a.c0 == 0 && a.c1 % 2 == 1)

end Fp2

end NearCrypto.Pairing
