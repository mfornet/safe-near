import NearCrypto.Pairing.Group

/-!
# The tower `Fp2 ⊂ Fp6 ⊂ Fp12`, fast version

`Fp6 = Fp2[v] / (v³ - ξ)` and `Fp12 = Fp6[w] / (w² - v)` with `ξ = a + u` (`a = 9` for BN254, `1`
for BLS12-381), so `w⁶ = ξ`. Products use Karatsuba at both levels (six `Fp2` products for
`Fp6`, three `Fp6` products for `Fp12`) and squarings the complex method. The context carries the
prime, `a` and the Frobenius constants `γᵢ = ξ^(i (p - 1) / 6)` of `w ↦ w^p`.
-/

namespace NearCrypto.Pairing

/-- The prime, `ξ = a + u` and the Frobenius constants `γ₁ … γ₅`. -/
structure Ctx where
  p : Nat
  a : Nat
  gamma : Array Fp2

namespace Ctx

def ofParams (p a : Nat) : Ctx :=
  let xi : Fp2 := ⟨a, 1⟩
  { p, a, gamma := (List.range 5).toArray.map fun i => Fp2.pow p xi ((i + 1) * ((p - 1) / 6)) }

/-- `ξ x`. -/
def mulXi (c : Ctx) (x : Fp2) : Fp2 :=
  if c.a == 1 then ⟨Fp2.subMod c.p x.c0 x.c1, Fp2.addMod c.p x.c0 x.c1⟩
  else ⟨(c.a * x.c0 + (c.p - x.c1)) % c.p, (x.c0 + c.a * x.c1) % c.p⟩

end Ctx

/-- `c0 + c1 v + c2 v²`. -/
structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2
  deriving BEq, Inhabited

/-- `c0 + c1 w`. -/
structure Fp12 where
  c0 : Fp6
  c1 : Fp6
  deriving BEq, Inhabited

namespace Fp6

def zero : Fp6 :=
  ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩

def one : Fp6 :=
  ⟨Fp2.one, Fp2.zero, Fp2.zero⟩

def add (c : Ctx) (a b : Fp6) : Fp6 :=
  ⟨Fp2.add c.p a.c0 b.c0, Fp2.add c.p a.c1 b.c1, Fp2.add c.p a.c2 b.c2⟩

def sub (c : Ctx) (a b : Fp6) : Fp6 :=
  ⟨Fp2.sub c.p a.c0 b.c0, Fp2.sub c.p a.c1 b.c1, Fp2.sub c.p a.c2 b.c2⟩

def neg (c : Ctx) (a : Fp6) : Fp6 :=
  ⟨Fp2.neg c.p a.c0, Fp2.neg c.p a.c1, Fp2.neg c.p a.c2⟩

/-- Product, six `Fp2` products. -/
def mul (c : Ctx) (a b : Fp6) : Fp6 :=
  let p := c.p
  let v0 := Fp2.mul p a.c0 b.c0
  let v1 := Fp2.mul p a.c1 b.c1
  let v2 := Fp2.mul p a.c2 b.c2
  let t0 := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.addU a.c1 a.c2) (Fp2.addU b.c1 b.c2)) v1) v2
  let t1 := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.addU a.c0 a.c1) (Fp2.addU b.c0 b.c1)) v0) v1
  let t2 := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.addU a.c0 a.c2) (Fp2.addU b.c0 b.c2)) v0) v2
  ⟨Fp2.add p v0 (c.mulXi t0), Fp2.add p t1 (c.mulXi v2), Fp2.add p t2 v1⟩

/-- Square (Chung-Hasan). -/
def sqr (c : Ctx) (a : Fp6) : Fp6 :=
  let p := c.p
  let s0 := Fp2.sqr p a.c0
  let ab := Fp2.mul p a.c0 a.c1
  let s1 := Fp2.add p ab ab
  let s2 := Fp2.sqr p (Fp2.add p (Fp2.sub p a.c0 a.c1) a.c2)
  let bc := Fp2.mul p a.c1 a.c2
  let s3 := Fp2.add p bc bc
  let s4 := Fp2.sqr p a.c2
  ⟨Fp2.add p s0 (c.mulXi s3), Fp2.add p s1 (c.mulXi s4),
    Fp2.sub p (Fp2.sub p (Fp2.add p (Fp2.add p s1 s2) s3) s0) s4⟩

/-- Product by `v`. -/
def mulV (c : Ctx) (a : Fp6) : Fp6 :=
  ⟨c.mulXi a.c2, a.c0, a.c1⟩

/-- Product by an element of `Fp2` placed at `1`. -/
def scale (c : Ctx) (a : Fp6) (k : Fp2) : Fp6 :=
  ⟨Fp2.mul c.p a.c0 k, Fp2.mul c.p a.c1 k, Fp2.mul c.p a.c2 k⟩

/-- Product by `b0 + b1 v`: five `Fp2` products. -/
def mulBy01 (c : Ctx) (a : Fp6) (b0 b1 : Fp2) : Fp6 :=
  let p := c.p
  let v0 := Fp2.mul p a.c0 b0
  let v1 := Fp2.mul p a.c1 b1
  let w := Fp2.mul p a.c2 b1
  let u := Fp2.mul p a.c2 b0
  let cross := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.addU a.c0 a.c1) (Fp2.addU b0 b1)) v0) v1
  ⟨Fp2.add p v0 (c.mulXi w), cross, Fp2.add p v1 u⟩

/-- Product by `b1 v`: three `Fp2` products. -/
def mulBy1 (c : Ctx) (a : Fp6) (b1 : Fp2) : Fp6 :=
  ⟨c.mulXi (Fp2.mul c.p a.c2 b1), Fp2.mul c.p a.c0 b1, Fp2.mul c.p a.c1 b1⟩

/-- The inverse. -/
def inv (c : Ctx) (a : Fp6) : Fp6 :=
  let p := c.p
  let t0 := Fp2.sub p (Fp2.sqr p a.c0) (c.mulXi (Fp2.mul p a.c1 a.c2))
  let t1 := Fp2.sub p (c.mulXi (Fp2.sqr p a.c2)) (Fp2.mul p a.c0 a.c1)
  let t2 := Fp2.sub p (Fp2.sqr p a.c1) (Fp2.mul p a.c0 a.c2)
  let d :=
    Fp2.add p (Fp2.mul p a.c0 t0) (c.mulXi (Fp2.add p (Fp2.mul p a.c2 t1) (Fp2.mul p a.c1 t2)))
  let di := Fp2.inv p d
  ⟨Fp2.mul p t0 di, Fp2.mul p t1 di, Fp2.mul p t2 di⟩

end Fp6

namespace Fp12

def one : Fp12 :=
  ⟨Fp6.one, Fp6.zero⟩

def mul (c : Ctx) (a b : Fp12) : Fp12 :=
  let v0 := Fp6.mul c a.c0 b.c0
  let v1 := Fp6.mul c a.c1 b.c1
  ⟨Fp6.add c v0 (Fp6.mulV c v1),
    Fp6.sub c (Fp6.sub c (Fp6.mul c (Fp6.add c a.c0 a.c1) (Fp6.add c b.c0 b.c1)) v0) v1⟩

def sqr (c : Ctx) (a : Fp12) : Fp12 :=
  let ab := Fp6.mul c a.c0 a.c1
  let t := Fp6.mul c (Fp6.add c a.c0 a.c1) (Fp6.add c a.c0 (Fp6.mulV c a.c1))
  ⟨Fp6.sub c (Fp6.sub c t ab) (Fp6.mulV c ab), Fp6.add c ab ab⟩

/-- `f ^ (p⁶)`, the conjugate; the inverse on the cyclotomic subgroup. -/
def conj (c : Ctx) (a : Fp12) : Fp12 :=
  ⟨a.c0, Fp6.neg c a.c1⟩

def inv (c : Ctx) (a : Fp12) : Fp12 :=
  let t := Fp6.inv c (Fp6.sub c (Fp6.sqr c a.c0) (Fp6.mulV c (Fp6.sqr c a.c1)))
  ⟨Fp6.mul c a.c0 t, Fp6.neg c (Fp6.mul c a.c1 t)⟩

/-- `f ^ p`: the conjugate of each coefficient of `w^i` times `γᵢ`. -/
def frob (c : Ctx) (a : Fp12) : Fp12 :=
  let p := c.p
  let g := fun (i : Nat) (x : Fp2) => Fp2.mul p (Fp2.conj p x) c.gamma[i - 1]!
  ⟨⟨Fp2.conj p a.c0.c0, g 2 a.c0.c1, g 4 a.c0.c2⟩, ⟨g 1 a.c1.c0, g 3 a.c1.c1, g 5 a.c1.c2⟩⟩

/-- `f ^ (p²)`. -/
def frob2 (c : Ctx) (a : Fp12) : Fp12 :=
  frob c (frob c a)

/-- `f ^ e`, square and multiply from the top bit. -/
def pow (c : Ctx) (a : Fp12) (e : Nat) : Fp12 :=
  Id.run do
    let mut r := one
    for i in [0:e.log2 + 1] do
      r := sqr c r
      if e.testBit (e.log2 - i) then
        r := mul c r a
    return r

/-- Squaring in the cyclotomic subgroup (Granger-Scott): the six `Fp2` coefficients of `f` are
three pairs, each squared in `Fp4 = Fp2[w³] / (w⁶ - ξ)`; nine `Fp2` squarings in place of the
generic squaring's twelve `Fp2` products. Valid when `f ^ (p⁴ - p² + 1) = 1`, that is after the
easy part of the final exponentiation. -/
def cycSqr (c : Ctx) (f : Fp12) : Fp12 :=
  let p := c.p
  let fp4 := fun (a b : Fp2) =>
    let t0 := Fp2.sqr p a
    let t1 := Fp2.sqr p b
    (Fp2.add p (c.mulXi t1) t0, Fp2.sub p (Fp2.sub p (Fp2.sqr p (Fp2.add p a b)) t0) t1)
  -- `3 t - 2 z` and `3 t + 2 z`
  let minus := fun (t z : Fp2) =>
    let d := Fp2.sub p t z
    Fp2.add p (Fp2.add p d d) t
  let plus := fun (t z : Fp2) =>
    let d := Fp2.add p t z
    Fp2.add p (Fp2.add p d d) t
  let (t0, t1) := fp4 f.c0.c0 f.c1.c1
  let z0 := minus t0 f.c0.c0
  let z1 := plus t1 f.c1.c1
  let (u0, u1) := fp4 f.c1.c0 f.c0.c2
  let (v0, v1) := fp4 f.c0.c1 f.c1.c2
  let z4 := minus u0 f.c0.c1
  let z5 := plus u1 f.c1.c2
  let w := c.mulXi v1
  let z2 := plus w f.c1.c0
  let z3 := minus v0 f.c0.c2
  ⟨⟨z0, z4, z3⟩, ⟨z2, z1, z5⟩⟩

/-- `f ^ e` for `f` in the cyclotomic subgroup: its squaring, and the non-adjacent form of `e`
(the inverse is the conjugate). -/
def powCyc (c : Ctx) (a : Fp12) (e : Nat) : Fp12 :=
  Id.run do
    let forms := Jac.wnaf e 2
    let inv := conj c a
    let mut r := one
    for i in [0:forms.size] do
      r := cycSqr c r
      let d := forms.getD (forms.size - 1 - i) 0
      if d > 0 then
        r := mul c r a
      else if d < 0 then
        r := mul c r inv
    return r

end Fp12

end NearCrypto.Pairing
