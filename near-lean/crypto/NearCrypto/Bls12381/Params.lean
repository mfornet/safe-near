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

/-- The generator of `G1`. -/
def g1Gen : G1 :=
  some
    (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
      0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

/-- The generator of `G2`. -/
def g2Gen : G2 :=
  some
    (⟨0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
        0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e⟩,
      ⟨0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
        0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be⟩)

end NearCrypto.Bls12381
