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
  ⟨(c.a * x.c0 + (c.p - x.c1)) % c.p, (x.c0 + c.a * x.c1) % c.p⟩

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
  let t0 := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.add p a.c1 a.c2) (Fp2.add p b.c1 b.c2)) v1) v2
  let t1 := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.add p a.c0 a.c1) (Fp2.add p b.c0 b.c1)) v0) v1
  let t2 := Fp2.sub p (Fp2.sub p (Fp2.mul p (Fp2.add p a.c0 a.c2) (Fp2.add p b.c0 b.c2)) v0) v2
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

/-- Product with the coefficients of `b` that are zero skipped (schoolbook). -/
def mulSparse (c : Ctx) (a b : Fp6) : Fp6 :=
  let p := c.p
  let bs := #[b.c0, b.c1, b.c2]
  let as := #[a.c0, a.c1, a.c2]
  let r :=
    Id.run do
      let mut r : Array Fp2 := Array.replicate 5 Fp2.zero
      for j in [0:3] do
        if !(bs[j]!).isZero then
          for i in [0:3] do
            r := r.modify (i + j) fun x => Fp2.add p x (Fp2.mul p as[i]! bs[j]!)
      return r
  ⟨Fp2.add p r[0]! (c.mulXi r[3]!), Fp2.add p r[1]! (c.mulXi r[4]!), r[2]!⟩

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

end Fp12

end NearCrypto.Pairing
