import NearCrypto.Pairing.Spec
import NearCrypto.Pairing.Tower

/-!
# The optimal ate pairing, fast version

The same pairing as `Pairing.Spec` up to the final exponentiation's fixed power (none here: the
result equals the reference's): one Miller loop for all pairs, so one squaring of the accumulator
per bit; the points `T` of the twist are kept in Jacobian coordinates, so a step costs no
inversion; the line through `T` is evaluated at `P` as a sparse `Fp12` element.

With `T = (X : Y : Z)`, the tangent at `T` scaled by `2 Y Z³ ∈ Fp2` (a factor the final
exponentiation removes) is, with `E = 3 X²`, `Z' = 2 Y Z` the new `Z`,

* constant `E X - 2 Y²`,
* `-E Z² x_P` for the abscissa of `P`,
* `Z' Z² y_P` for the ordinate of `P`,

and the line through `T` and the affine `Q = (x_q, y_q)`, scaled by `Z H` (`H = x_q Z² - X`),
with `R = y_q Z³ - Y`, has constant `R x_q - Z H y_q`, abscissa term `-R x_P` and ordinate term
`Z H y_P`. A D-type twist puts them at `1, w, w³` (ordinate, abscissa, constant) and an M-type
twist (after multiplying the line by `w³`) at `1, v, w³` (constant, abscissa, ordinate).

The final exponentiation is the easy part `(p⁶ - 1)(p² + 1)` with conjugation and Frobenius
maps, then the hard part `(p⁴ - p² + 1) / r` from its expansion in powers of `x`:
`λ₀ + λ₁ p + λ₂ p² + p³` for BN and `((x - 1)² / 3)(x + p)(x² + p² - 1) + 1` for BLS.
-/

namespace NearCrypto.Pairing

/-- A curve with the constants the fast pairing needs. -/
structure Params where
  curve : Curve
  ctx : Ctx
  /-- `|x|`, where the curve parameter is `±x`. -/
  x : Nat
  /-- The Frobenius of the twist: multipliers of the conjugated coordinates. -/
  twX : Fp2
  twY : Fp2

namespace Params

def ofCurve (c : Curve) (x : Nat) : Params :=
  let xi := c.xi
  let cx := Fp2.pow c.p xi ((c.p - 1) / 3)
  let cy := Fp2.pow c.p xi ((c.p - 1) / 2)
  { curve := c, ctx := Ctx.ofParams c.p c.a, x, twX := if c.dTwist then cx else Fp2.inv c.p cx,
    twY := if c.dTwist then cy else Fp2.inv c.p cy }

end Params

namespace Impl

/-- A point of the twist, Jacobian. -/
abbrev T3 :=
  Fp2 × Fp2 × Fp2

/-- `f · l` for the line with ordinate, abscissa and constant terms `cy`, `cx`, `k`: thirteen
`Fp2` products. A D-type twist puts them at `1`, `w`, `w³`, so `l = (cy, 0, 0) + (cx, k, 0) w`; an
M-type twist at `1`, `v`, `w³`, so `l = (k, cx, 0) + (0, cy, 0) w`. -/
def mulLine (P : Params) (f : Fp12) (cy cx k : Fp2) : Fp12 :=
  let c := P.ctx
  let (v0, v1, cross) :=
    if P.curve.dTwist then
      (Fp6.scale c f.c0 cy, Fp6.mulBy01 c f.c1 cx k,
        Fp6.mulBy01 c (Fp6.add c f.c0 f.c1) (Fp2.add c.p cy cx) k)
    else
      (Fp6.mulBy01 c f.c0 k cx, Fp6.mulBy1 c f.c1 cy,
        Fp6.mulBy01 c (Fp6.add c f.c0 f.c1) k (Fp2.add c.p cx cy))
  ⟨Fp6.add c v0 (Fp6.mulV c v1), Fp6.sub c (Fp6.sub c cross v0) v1⟩

/-- Double `T` and return the line (tangent) at `P = (xP, yP)`. -/
def dblStep (P : Params) (T : T3) (xP yP : Nat) : T3 × (Fp2 × Fp2 × Fp2) :=
  let p := P.ctx.p
  let (X, Y, Z) := T
  let A := Fp2.sqr p X
  let B := Fp2.sqr p Y
  let C := Fp2.sqr p B
  let D := Fp2.sub p (Fp2.sub p (Fp2.sqr p (Fp2.add p X B)) A) C
  let D := Fp2.add p D D
  let E := Fp2.add p (Fp2.add p A A) A
  let F := Fp2.sqr p E
  let X3 := Fp2.sub p F (Fp2.add p D D)
  let C8 := Fp2.add p C C
  let C8 := Fp2.add p C8 C8
  let C8 := Fp2.add p C8 C8
  let Y3 := Fp2.sub p (Fp2.mul p E (Fp2.sub p D X3)) C8
  let YZ := Fp2.mul p Y Z
  let Z3 := Fp2.add p YZ YZ
  let Z2 := Fp2.sqr p Z
  let cy := Fp2.scale p (Fp2.mul p Z3 Z2) yP
  let cx := Fp2.scale p (Fp2.neg p (Fp2.mul p E Z2)) xP
  let k := Fp2.sub p (Fp2.mul p E X) (Fp2.add p B B)
  ((X3, Y3, Z3), (cy, cx, k))

/-- Add the affine `Q` to `T` and return the line through them at `P`. -/
def addStep (P : Params) (T : T3) (Q : Fp2 × Fp2) (xP yP : Nat) : T3 × (Fp2 × Fp2 × Fp2) :=
  let p := P.ctx.p
  let (X, Y, Z) := T
  let Z2 := Fp2.sqr p Z
  let U2 := Fp2.mul p Q.1 Z2
  let S2 := Fp2.mul p (Fp2.mul p Q.2 Z2) Z
  let H := Fp2.sub p U2 X
  let R := Fp2.sub p S2 Y
  let ZH := Fp2.mul p Z H
  let HH := Fp2.sqr p H
  let I := Fp2.add p HH HH
  let I := Fp2.add p I I
  let J := Fp2.mul p H I
  let r := Fp2.add p R R
  let V := Fp2.mul p X I
  let X3 := Fp2.sub p (Fp2.sub p (Fp2.sqr p r) J) (Fp2.add p V V)
  let YJ := Fp2.mul p Y J
  let Y3 := Fp2.sub p (Fp2.mul p r (Fp2.sub p V X3)) (Fp2.add p YJ YJ)
  let Z3 := Fp2.add p ZH ZH
  let cy := Fp2.scale p ZH yP
  let cx := Fp2.scale p (Fp2.neg p R) xP
  let k := Fp2.sub p (Fp2.mul p R Q.1) (Fp2.mul p ZH Q.2)
  ((X3, Y3, Z3), (cy, cx, k))

/-- The product of the Miller values of the pairs `((xP, yP), Q)`, `P` and `Q` finite. -/
def millerLoop (P : Params) (pairs : Array ((Nat × Nat) × (Fp2 × Fp2))) : Fp12 :=
  Id.run do
    let c := P.curve
    let ctx := P.ctx
    let pairs := if c.xNeg then pairs.map fun ((x, y), q) => ((x, (c.p - y) % c.p), q) else pairs
    let mut f := Fp12.one
    let mut ts : Array T3 := pairs.map fun (_, q) => (q.1, q.2, Fp2.one)
    for i in [0:c.loop.log2] do
      f := Fp12.sqr ctx f
      for j in [0:pairs.size] do
        let ((xP, yP), _) := pairs[j]!
        let (t, l) := dblStep P ts[j]! xP yP
        ts := ts.set! j t
        f := mulLine P f l.1 l.2.1 l.2.2
      if c.loop.testBit (c.loop.log2 - 1 - i) then
        for j in [0:pairs.size] do
          let ((xP, yP), q) := pairs[j]!
          let (t, l) := addStep P ts[j]! q xP yP
          ts := ts.set! j t
          f := mulLine P f l.1 l.2.1 l.2.2
    if c.bn then
      for j in [0:pairs.size] do
        let ((xP, yP), q) := pairs[j]!
        let frobQ := fun (z : Fp2 × Fp2) =>
          (Fp2.mul c.p (Fp2.conj c.p z.1) P.twX, Fp2.mul c.p (Fp2.conj c.p z.2) P.twY)
        let q1 := frobQ q
        let q2 := frobQ q1
        let q2 := (q2.1, Fp2.neg c.p q2.2)
        let (t, l) := addStep P ts[j]! q1 xP yP
        f := mulLine P f l.1 l.2.1 l.2.2
        let (_, l) := addStep P t q2 xP yP
        f := mulLine P f l.1 l.2.1 l.2.2
    return f

/-- The hard part `f ^ ((p⁴ - p² + 1) / r)` of an element of the cyclotomic subgroup. -/
def hardPart (P : Params) (t : Fp12) : Fp12 :=
  let c := P.ctx
  let pow := Fp12.powCyc c
  let mul := Fp12.mul c
  if P.curve.bn then
    let fx := pow t P.x
    let fx2 := pow fx P.x
    let fx3 := pow fx2 P.x
    let inv := Fp12.conj c
    let y2 := mul (pow fx2 6) t
    let y1 := mul (inv (mul (pow fx3 36) (mul (pow fx2 18) (pow fx 12)))) t
    let y0 := mul (inv (mul (pow fx3 36) (mul (pow fx2 30) (pow fx 18)))) (pow (inv t) 2)
    mul (mul y0 (Fp12.frob c y1)) (mul (Fp12.frob2 c y2) (Fp12.frob c (Fp12.frob2 c t)))
  else
    -- x = -|x|: `a ^ x` is the conjugate of `a ^ |x|`
    let powX := fun a => Fp12.conj c (pow a P.x)
    let a := pow (pow t (P.x + 1)) ((P.x + 1) / 3)
    let b := mul (powX a) (Fp12.frob c a)
    let d := mul (mul (powX (powX b)) (Fp12.frob2 c b)) (Fp12.conj c b)
    mul d t

/-- `f ^ ((p¹² - 1) / r)`. -/
def finalExp (P : Params) (f : Fp12) : Fp12 :=
  let c := P.ctx
  let t := Fp12.mul c (Fp12.conj c f) (Fp12.inv c f)
  let t := Fp12.mul c (Fp12.frob2 c t) t
  hardPart P t

/-- Whether `∏ e(Pᵢ, Qᵢ) = 1`; infinities contribute one. -/
def pairingCheck (P : Params) (pairs : List (Option (Nat × Nat) × Option (Fp2 × Fp2))) : Bool :=
  let finite :=
    pairs.filterMap fun (a, q) =>
      match a, q with
      | some a, some q => some (a, q)
      | _, _ => none
  finalExp P (millerLoop P finite.toArray) == Fp12.one

end Impl

end NearCrypto.Pairing
