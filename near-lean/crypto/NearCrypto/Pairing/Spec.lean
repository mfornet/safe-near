import NearCrypto.Pairing.Group

/-!
# The optimal ate pairing, reference version

BN254 and BLS12-381 share one description. `E : y² = x³ + b` over `Fp`, the twist `E'` over
`Fp2 = Fp[u] / (u² + 1)` with `ξ = a + u`, `Fp12 = Fp[w] / (w¹² - 2 a w⁶ + a² + 1)` (so `w⁶ = ξ` and
`u = w⁶ - a`), kept as a flat array of twelve coefficients. `E'` is `y² = x³ + b / ξ` and untwisted by
`(x w², y w³)` (D-type, BN254), or `y² = x³ + b ξ` and untwisted by `(x / w², y / w³)` (M-type,
BLS12-381).

The Miller loop runs on the twist in affine coordinates and evaluates each line at `P` after
untwisting, with plain `Fp12` products; the final exponentiation is the power `(p¹² - 1) / r`.
Nothing here is fast. The loop is `6 x + 2` with the two Frobenius steps (BN254), or `|x|` with the
point `P` negated for the negative `x` of BLS12-381 (the Miller value of `-P` is the inverse, modulo
the final exponentiation, of the one of `P`). The check `∏ e(Pᵢ, Qᵢ) = 1` does not depend on the
power of the pairing used, so any nondegenerate reduced pairing gives the host function's answer.
-/

namespace NearCrypto.Pairing

/-- The parameters of a pairing-friendly curve of the two families used here. -/
structure Curve where
  /-- The field prime. -/
  p : Nat
  /-- The prime order of `G1` and `G2`. -/
  r : Nat
  /-- `E : y² = x³ + b`. -/
  b : Nat
  /-- `ξ = a + u`. -/
  a : Nat
  /-- D-type twist (`b / ξ`) or M-type (`b ξ`). -/
  dTwist : Bool
  /-- The Miller loop count: `6 x + 2` for BN, `|x|` for BLS. -/
  loop : Nat
  /-- Whether the loop is followed by the two Frobenius lines of BN curves. -/
  bn : Bool
  /-- Whether `x` is negative (BLS12-381). -/
  xNeg : Bool

namespace Curve

def xi (c : Curve) : Fp2 :=
  ⟨c.a, 1⟩

/-- The coefficient of the twist. -/
def b2 (c : Curve) : Fp2 :=
  if c.dTwist then Fp2.scale c.p (Fp2.inv c.p c.xi) c.b else Fp2.scale c.p c.xi c.b

end Curve

namespace Spec

/-- An `Fp12` element: twelve coefficients of `1, w, …, w¹¹`. -/
abbrev F12 :=
  Array Nat

def one : F12 :=
  #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Product, reducing with `w¹² = 2 a w⁶ - (a² + 1)`. -/
def mul (c : Curve) (x y : F12) : F12 :=
  Id.run do
    let mut t := Array.replicate 23 0
    for i in [0:12] do
      let xi := x[i]!
      if xi != 0 then
        for j in [0:12] do
          t := t.modify (i + j) (· + xi * y[j]!)
    for i in [0:11] do
      let k := 22 - i
      let v := t[k]! % c.p
      t := t.modify (k - 6) (· + 2 * c.a * v)
      t := t.modify (k - 12) (· + (c.p - (c.a * c.a + 1) % c.p) * v)
    return Array.ofFn (n := 12) fun i => t[i.val]! % c.p

def add (c : Curve) (x y : F12) : F12 :=
  Array.ofFn (n := 12) fun i => (x[i.val]! + y[i.val]!) % c.p

def sub (c : Curve) (x y : F12) : F12 :=
  Array.ofFn (n := 12) fun i => (x[i.val]! + (c.p - y[i.val]!)) % c.p

def pow (c : Curve) (x : F12) (e : Nat) : F12 :=
  Id.run do
    let mut r := one
    let mut b := x
    for i in [0:e.log2 + 1] do
      if e.testBit i then
        r := mul c r b
      b := mul c b b
    return r

/-- `w ^ k`. -/
def wPow (k : Nat) : F12 :=
  Array.ofFn (n := 12) fun i => if i.val == k then 1 else 0

/-- `Fp2 ⊂ Fp12` by `u = w⁶ - a`. -/
def ofFp2 (c : Curve) (z : Fp2) : F12 :=
  Array.ofFn (n := 12) fun i =>
    if i.val == 0 then (z.c0 + (c.p - c.a * z.c1 % c.p)) % c.p else if i.val == 6 then z.c1 else 0

def ofFp (x : Nat) : F12 :=
  Array.ofFn (n := 12) fun i => if i.val == 0 then x else 0

/-! ### The twist, affine -/

/-- A point of the twist; `none` is infinity. -/
abbrev TwPt :=
  Option (Fp2 × Fp2)

/-- The slope of the line through two twist points (the tangent when equal). -/
def slope (c : Curve) (P Q : Fp2 × Fp2) : Fp2 :=
  let p := c.p
  if P.1 == Q.1 then Fp2.mul p (Fp2.scale p (Fp2.sqr p P.1) 3) (Fp2.inv p (Fp2.scale p P.2 2))
  else Fp2.mul p (Fp2.sub p Q.2 P.2) (Fp2.inv p (Fp2.sub p Q.1 P.1))

def twAdd (c : Curve) : TwPt → TwPt → TwPt
  | none, Q => Q
  | P, none => P
  | some P, some Q =>
    if P.1 == Q.1 && (P.2 != Q.2 || P.2 == Fp2.zero) then none
    else
      let p := c.p
      let lam := slope c P Q
      let x3 := Fp2.sub p (Fp2.sub p (Fp2.sqr p lam) P.1) Q.1
      some (x3, Fp2.sub p (Fp2.mul p lam (Fp2.sub p P.1 x3)) P.2)

def twNeg (c : Curve) : TwPt → TwPt
  | none => none
  | some (x, y) => some (x, Fp2.neg c.p y)

def twOnCurve (c : Curve) : TwPt → Bool
  | none => true
  | some (x, y) => Fp2.sqr c.p y == Fp2.add c.p (Fp2.mul c.p (Fp2.sqr c.p x) x) c.b2

/-- The `p`-power Frobenius of the untwisted point, as a point of the twist. -/
def frobenius (c : Curve) (P : Fp2 × Fp2) : Fp2 × Fp2 :=
  let p := c.p
  let cx := Fp2.pow p c.xi ((p - 1) / 3)
  let cy := Fp2.pow p c.xi ((p - 1) / 2)
  let (cx, cy) := if c.dTwist then (cx, cy) else (Fp2.inv p cx, Fp2.inv p cy)
  (Fp2.mul p (Fp2.conj p P.1) cx, Fp2.mul p (Fp2.conj p P.2) cy)

/-- The untwisting map `E' → E(Fp12)`. -/
def untwist (c : Curve) (P : Fp2 × Fp2) : F12 × F12 :=
  if c.dTwist then (mul c (ofFp2 c P.1) (wPow 2), mul c (ofFp2 c P.2) (wPow 3))
  else
    let xiInv := ofFp2 c (Fp2.inv c.p c.xi)
    (mul c (mul c (ofFp2 c P.1) (wPow 4)) xiInv, mul c (mul c (ofFp2 c P.2) (wPow 3)) xiInv)

/-- The line through `T` and `Q` (the tangent if equal), untwisted, at `P ∈ E(Fp)`. -/
def line (c : Curve) (T Q : Fp2 × Fp2) (P : Nat × Nat) : F12 :=
  let lam := slope c T Q
  let (x, y) := untwist c T
  let slope12 :=
    if c.dTwist then mul c (ofFp2 c lam) (wPow 1)
    else mul c (mul c (ofFp2 c lam) (wPow 5)) (ofFp2 c (Fp2.inv c.p c.xi))
  sub c (sub c (ofFp P.2) y) (mul c slope12 (sub c (ofFp P.1) x))

/-- `P + Q` for points of finite result (the sum of two points of the prime-order group is
infinity only at the very end of a loop, where it is not used again). -/
def addPt (c : Curve) (P Q : Fp2 × Fp2) : Fp2 × Fp2 :=
  (twAdd c (some P) (some Q)).getD P

/-- The Miller value of the optimal ate loop of `Q ≠ O` at `P ≠ O`. -/
def miller (c : Curve) (Q : Fp2 × Fp2) (P : Nat × Nat) : F12 :=
  Id.run do
    let P := if c.xNeg then (P.1, (c.p - P.2) % c.p) else P
    let mut f := one
    let mut T := Q
    for i in [0:c.loop.log2] do
      f := mul c (mul c f f) (line c T T P)
      T := addPt c T T
      if c.loop.testBit (c.loop.log2 - 1 - i) then
        f := mul c f (line c T Q P)
        T := addPt c T Q
    if c.bn then
      let Q1 := frobenius c Q
      let Q2 := frobenius c Q1
      let Q2 := (Q2.1, Fp2.neg c.p Q2.2)
      f := mul c f (line c T Q1 P)
      T := addPt c T Q1
      f := mul c f (line c T Q2 P)
    return f

/-- `f ^ ((p¹² - 1) / r)`. -/
def finalExp (c : Curve) (f : F12) : F12 :=
  pow c f ((c.p ^ 12 - 1) / c.r)

/-- Whether `∏ e(Pᵢ, Qᵢ) = 1` for points of `G1` and `G2` (infinity contributes one). -/
def pairingCheck (c : Curve) (pairs : List (Option (Nat × Nat) × TwPt)) : Bool :=
  let f :=
    pairs.foldl
      (fun f (P, Q) =>
        match P, Q with
        | some P, some Q => mul c f (miller c Q P)
        | _, _ => f)
      one
  finalExp c f == one

end Spec

end NearCrypto.Pairing
