import NearCrypto.Pairing.Impl

/-!
# BLS12-381: parameters

`z = -0xd201000000010000` is the curve parameter (`x` in the BLS literature), `p` the field prime,
`r = z⁴ - z² + 1` the prime order of `G1` and `G2`, `E : y² = x³ + 4` over `Fp` and
`E' : y² = x³ + 4 (1 + u)` over `Fp2 = Fp[u] / (u² + 1)`, the M-type twist with `ξ = 1 + u`.
-/

namespace NearCrypto.Bls12381

open NearCrypto.Pairing

/-- The field prime. -/
def p : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- The order of `G1` and `G2`. -/
def r : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- `|z|`, where `z = -0xd201000000010000`. -/
def z : Nat :=
  0xd201000000010000

/-- The pairing: Miller loop of length `|z|` at the negated point. -/
def curve : Curve :=
  { p, r, b := 4, a := 1, dTwist := false, loop := z, bn := false, xNeg := true }

/-- The constants of the fast pairing. -/
def params : Params :=
  Params.ofCurve curve z

/-- A primitive cube root of unity of `Fp` such that `σ(x, y) = (β x, y)` satisfies
`σ²(P) = -[z²] P` on `G1`: the endomorphism of `blst`'s subgroup test. -/
def beta : Nat :=
  0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac

/-- The effective cofactor of `G2` (RFC 9380 section 8.8.2), from its 64-bit words, least
significant first. -/
def hEff : Nat :=
  let words : List Nat :=
    [0xe8020005aaa95551, 0x59894c0adebbf6b4, 0xe954cbc06689f6a3, 0x2ec0ec69d7477c1a,
      0x6d82bf015d1212b0, 0x329c2f178731db95, 0x9986ff031508ffe1, 0x88e2a8e9145ad768,
      0x584c6a0ea91b3528, 0x0bc69f08f2ee75b3]
  words.foldr (fun w acc => acc <<< 64 ||| w) 0

/-- The base field as a record. -/
def f1 : Fld Nat :=
  fpFld p

/-- The quadratic extension as a record. -/
def f2 : Fld Fp2 :=
  fp2Fld p

/-- A point of `G1`; `none` is infinity. -/
abbrev G1 :=
  Option (Nat × Nat)

/-- A point of `G2`; `none` is infinity. -/
abbrev G2 :=
  Option (Fp2 × Fp2)

end NearCrypto.Bls12381
