import NearCrypto.Bls12381.Params
import NearCrypto.Bls12381.Isogeny

/-!
# The maps `Fp → G1` and `Fp2 → G2` of RFC 9380

`bls12381_map_fp_to_g1` and `bls12381_map_fp2_to_g2` call `blst_map_to_g1` and `blst_map_to_g2`
with one field element: `map_to_curve` of the suites `BLS12381G1_XMD:SHA-256_SSWU_RO_` and
`BLS12381G2_XMD:SHA-256_SSWU_RO_` without the hashing, that is the simplified SWU map (RFC 9380
section 6.6.2) onto the isogenous curve `y² = x³ + A' x + B'` with `Z = 11` (`G1`) or
`Z = -2 - u` (`G2`), the isogeny of degree 11 or 3 (appendix E.2, E.3) onto `E`, and the clearing
of the cofactor: multiplication by `1 - z` for `G1`, and for `G2` multiplication by `h_eff`, which
`blst` computes as `[z² - z - 1] P + [z - 1] ψ(P) + ψ²(2 P)` (Budroni and Pintore).
-/

namespace NearCrypto.Bls12381

open NearCrypto.Pairing

/-- A field with the extra operations of the SSWU map. -/
structure SField (α : Type) where
  F : Fld α
  sqrt : α → Option α
  sgn0 : α → Bool
  ofNat : Nat → α

/-- Simplified SWU (RFC 9380 section 6.6.2) onto `y² = x³ + A x + B` with the non-residue `Z`;
`1 / 0` is `0`. The sign of `y` is the sign of `u`. -/
def sswu {α : Type} (K : SField α) (A B Z u : α) : α × α :=
  let F := K.F
  let zu2 := F.mul Z (F.mul u u)
  let tv1 := F.inv (F.add (F.mul zu2 zu2) zu2)
  let x1 :=
    if F.isZero tv1 then F.mul B (F.inv (F.mul Z A))
    else F.mul (F.neg (F.mul B (F.inv A))) (F.add F.one tv1)
  let g := fun x => F.add (F.mul (F.add (F.mul x x) A) x) B
  let x2 := F.mul zu2 x1
  let (x, y) :=
    match K.sqrt (g x1) with
    | some y => (x1, y)
    | none => (x2, (K.sqrt (g x2)).getD F.zero)
  (x, if K.sgn0 u == K.sgn0 y then y else F.neg y)

/-- `∑ cᵢ xⁱ`, with a leading coefficient `1` of degree `cs.size` when `monic`. -/
def horner {α : Type} (F : Fld α) (cs : Array α) (monic : Bool) (x : α) : α :=
  let top := if monic then F.one else cs.getD (cs.size - 1) F.zero
  let n := if monic then cs.size else cs.size - 1
  (List.range n).foldl (fun acc i => F.add (F.mul acc x) (cs.getD (n - 1 - i) F.zero)) top

/-- The isogeny `(x, y) ↦ (xNum / xDen, y yNum / yDen)`; a zero denominator is infinity. -/
def isogeny {α : Type} (F : Fld α) (xNum xDen yNum yDen : Array α) (pt : α × α) : Option (α × α) :=
  let xd := horner F xDen true pt.1
  let yd := horner F yDen true pt.1
  if F.isZero xd || F.isZero yd then none
  else
    some
      (F.mul (horner F xNum false pt.1) (F.inv xd),
        F.mul pt.2 (F.mul (horner F yNum false pt.1) (F.inv yd)))

namespace HashToCurve

def sfp : SField Nat :=
  { F := f1, sqrt := sqrtMod p, sgn0 := (· % 2 == 1), ofNat := (· % p) }

def sfp2 : SField Fp2 :=
  { F := f2, sqrt := Fp2.sqrt p, sgn0 := Fp2.sgn0, ofNat := fun n => ⟨n % p, 0⟩ }

/-- The coefficients over `Fp2` from consecutive pairs. -/
def fp2s (a : Array Nat) : Array Fp2 :=
  (Array.range (a.size / 2)).map fun i => ⟨a[2 * i]!, a[2 * i + 1]!⟩

/-- `map_to_curve` onto `E`, before clearing the cofactor: `none` is infinity. -/
def mapToE1 (u : Nat) : G1 :=
  isogeny f1 Isogeny.xNum1 Isogeny.xDen1 Isogeny.yNum1 Isogeny.yDen1
    (sswu sfp (Isogeny.a1[0]!) (Isogeny.b1[0]!) 11 (u % p))

def mapToE2 (u : Fp2) : G2 :=
  let a := (fp2s Isogeny.a2)[0]!
  let b := (fp2s Isogeny.b2)[0]!
  isogeny f2 (fp2s Isogeny.xNum2) (fp2s Isogeny.xDen2) (fp2s Isogeny.yNum2) (fp2s Isogeny.yDen2)
    (sswu sfp2 a b ⟨p - 2, p - 1⟩ u)

/-- `-B / A` of the isogenous curve of `E1`. -/
def negBOverA : Nat :=
  (p - Isogeny.b1[0]! * invMod p Isogeny.a1[0]! % p) % p

/-- `B / (Z A)`, the abscissa when the denominator of the map vanishes. -/
def bOverZA : Nat :=
  Isogeny.b1[0]! * invMod p (11 * Isogeny.a1[0]! % p) % p

/-- `sqrt (-Z³)` for `Z = 11` (`-Z` is a square as `-1` and `Z` are not). -/
def sqrtMinusZ3 : Nat :=
  (sqrtMod p (p - 11 ^ 3)).getD 0

/-- The fast version of `mapToE1` (the same map): when `g(x₁)` is not a square then `-g(x₁)` is, with
root `g(x₁)^((p+1)/4)`, and the ordinate for `x₂ = Z u² x₁` is that root times `sqrt (-Z³) u³`
(`g(x₂) = Z³ u⁶ g(x₁)`); one inversion in the isogeny. -/
def mapToE1Fast (u : Nat) : G1 :=
  let u := u % p
  let u2 := u * u % p
  let zu2 := 11 * u2 % p
  let den := (zu2 * zu2 + zu2) % p
  let x1 := if den == 0 then bOverZA else negBOverA * (1 + invMod p den) % p
  let g1 := ((x1 * x1 + Isogeny.a1[0]!) % p * x1 + Isogeny.b1[0]!) % p
  let t := powMod p g1 ((p + 1) / 4)
  let (x, y) :=
    if t * t % p == g1 then (x1, t) else (zu2 * x1 % p, sqrtMinusZ3 * t % p * (u2 * u % p) % p)
  let y := if (u % 2 == 1) == (y % 2 == 1) then y else (p - y) % p
  let horner := fun (cs : Array Nat) (monic : Bool) => horner f1 cs monic x
  let xd := horner Isogeny.xDen1 true
  let yd := horner Isogeny.yDen1 true
  if xd == 0 || yd == 0 then none
  else
    let i := invMod p (xd * yd % p)
    some
      (horner Isogeny.xNum1 false * yd % p * i % p,
        y * horner Isogeny.yNum1 false % p * xd % p * i % p)

/-- The clearing of the cofactor of `G1`: `[1 - z] P = [|z| + 1] P`. -/
def clear1 (P : G1) : G1 :=
  Jac.toAffine f1 (Jac.mul f1 (Jac.ofAffine f1 P) (z + 1))

/-- The reference clearing for `G2`: the multiplication by `h_eff`. -/
def clear2Spec (P : G2) : G2 :=
  Jac.toAffine f2 (Jac.mul f2 (Jac.ofAffine f2 P) hEff)

/-- `ψ` on a Jacobian point of the twist: the conjugates, with `X` and `Y` scaled. -/
def psi (J : Jac Fp2) : Jac Fp2 :=
  ⟨Fp2.mul p (Fp2.conj p J.x) params.twX, Fp2.mul p (Fp2.conj p J.y) params.twY, Fp2.conj p J.z⟩

/-- `blst`'s clearing for `G2`: `[z² - z - 1] P + [z - 1] ψ(P) + ψ²(2 P)`. -/
def clear2Impl (P : G2) : G2 :=
  let Q := Jac.ofAffine f2 P
  let out := psi (psi (Jac.dbl f2 Q))
  let t0 := Jac.neg f2 Q
  let t1 := psi t0
  let out := Jac.add f2 (Jac.add f2 out t0) t1
  -- `[-z] Q` is `[|z|] Q`, `z` being negative
  let u0 := Jac.add f2 (Jac.mul f2 Q z) Q
  let u0 := Jac.add f2 u0 t1
  Jac.toAffine f2 (Jac.add f2 out (Jac.mul f2 u0 z))

end HashToCurve

end NearCrypto.Bls12381
