import NearCrypto.Pairing.Impl

/-!
# alt_bn128 (BN254): the VM's pairing host functions

`alt_bn128_g1_multiexp`, `alt_bn128_g1_sum` and `alt_bn128_pairing_check` exactly as
`near-vm-runner` 0.37.4 runs them (`logic/alt_bn128.rs`, over `zeropool-bn` 0.5.11):

* **Encodings** are little-endian. A field element `Fq` is 32 bytes `< q` (`Fq::from_u256` rejects
  `q` and above); a scalar `Fr` is 32 bytes `< r` (`Fr::new`). `G1` is `x ‖ y` (64 bytes) and the
  pair `(0, 0)` is the point at infinity; any other pair must satisfy `y² = x³ + 3`
  (`AffineG1::new`; the group has prime order, so nothing else is checked). `Fq2` is
  `re ‖ im` and `G2` is `x ‖ y` (128 bytes), `(0, 0)` infinity, otherwise on the twist
  `y² = x³ + 3 / (9 + i)` **and in the subgroup of order `r`** (`AffineG2::new`: `[r] P = O`).
* **`g1_multiexp`**: the input is a multiple of 96 bytes, `(G1, Fr)` each; the result is
  `∑ kᵢ Pᵢ` as 64 bytes (zeros for infinity). **`g1_sum`**: a multiple of 65 bytes, a sign byte
  (0 positive, 1 negative, anything else an error) and a `G1`. **`pairing_check`**: a multiple of
  192 bytes, `(G1, G2)` each; true when `∏ e(Pᵢ, Qᵢ) = 1` (an infinity contributes one, so the empty
  input is true).
* A wrong length or any invalid element is an error of the VM (`AltBn128InvalidInput`), here
  `Except.error`; the functions return what the host function writes to its register (or, for
  the pairing check, the value it returns).

`Spec` is built on the reference pairing (`Pairing.Spec`); `Impl` is the fast version.
-/

namespace NearCrypto.Bn254

open NearCrypto.Pairing

/-- The field prime. -/
def p : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The order of `G1`, `G2` and the scalar field. -/
def r : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The curve and its pairing: `x = 4965661367192848881`, loop `6 x + 2`. -/
def curve : Curve :=
  { p, r, b := 3, a := 9, dTwist := true, loop := 29793968203157093288, bn := true, xNeg := false }

/-- A point of `G1`; `none` is infinity. -/
abbrev G1 :=
  Option (Nat × Nat)

/-- A point of `G2`; `none` is infinity. -/
abbrev G2 :=
  Option (Fp2 × Fp2)

/-- The operations the host functions are built from. -/
structure Ops where
  /-- `∑ ± Pᵢ` (the flag is the sign: true negates). -/
  g1Sum : List (Bool × G1) → G1
  /-- `∑ kᵢ Pᵢ`. -/
  g1Multiexp : List (G1 × Nat) → G1
  /-- Whether a point of the twist is in the subgroup of order `r`. -/
  inG2 : Fp2 × Fp2 → Bool
  /-- Whether `∏ e(Pᵢ, Qᵢ) = 1`. -/
  pairingCheck : List (G1 × G2) → Bool

/-! ### Encodings -/

/-- `Fq::from_u256`: 32 little-endian bytes below `q`. -/
def decodeFq (b : ByteArray) (off : Nat) : Option Nat :=
  let v := leNat b off 32
  if v < p then some v else none

def decodeFq2 (b : ByteArray) (off : Nat) : Option Fp2 := do
  let c0 ← decodeFq b off
  let c1 ← decodeFq b (off + 32)
  pure ⟨c0, c1⟩

/-- `decode_g1`: `(0, 0)` is infinity, any other pair must be on `y² = x³ + 3`. -/
def decodeG1 (b : ByteArray) (off : Nat) : Option G1 := do
  let x ← decodeFq b off
  let y ← decodeFq b (off + 32)
  if x == 0 && y == 0 then
    pure none
  else if y * y % p == (x * x % p * x + 3) % p then
    pure (some (x, y))
  else
    none

/-- `decode_g2`: `(0, 0)` is infinity, any other pair must be on the twist and in the subgroup. -/
def decodeG2 (ops : Ops) (b : ByteArray) (off : Nat) : Option G2 := do
  let x ← decodeFq2 b off
  let y ← decodeFq2 b (off + 64)
  if x.isZero && y.isZero then
    pure none
  else if Pairing.Spec.twOnCurve curve (some (x, y)) && ops.inG2 (x, y) then
    pure (some (x, y))
  else
    failure

/-- `encode_g1`: 64 little-endian bytes, zeros for infinity. -/
def encodeG1 : G1 → ByteArray
  | none => zeros 64
  | some (x, y) => toLe x 32 ++ toLe y 32

/-- `decode_bool`: 0 or 1. -/
def decodeBool (b : ByteArray) (off : Nat) : Option Bool :=
  match b.get! off with
  | 0 => some false
  | 1 => some true
  | _ => none

/-! ### Host functions -/

section Host

variable (ops : Ops)

/-- `alt_bn128_g1_multiexp`: the 64 bytes written to the register. -/
def g1Multiexp (data : ByteArray) : Except String ByteArray := do
  if data.size % 96 != 0 then
    throw "length is not a multiple of 96"
  let mut terms := #[]
  for i in [0:data.size / 96] do
    let some pt := decodeG1 data (96 * i) | throw "invalid g1"
    let k := leNat data (96 * i + 64) 32
    if k ≥ r then
      throw "invalid fr"
    terms := terms.push (pt, k)
  pure (encodeG1 (ops.g1Multiexp terms.toList))

/-- `alt_bn128_g1_sum`: the 64 bytes written to the register. -/
def g1Sum (data : ByteArray) : Except String ByteArray := do
  if data.size % 65 != 0 then
    throw "length is not a multiple of 65"
  let mut terms := #[]
  for i in [0:data.size / 65] do
    let some sign := decodeBool data (65 * i) | throw "invalid bool"
    let some pt := decodeG1 data (65 * i + 1) | throw "invalid g1"
    terms := terms.push (sign, pt)
  pure (encodeG1 (ops.g1Sum terms.toList))

/-- `alt_bn128_pairing_check`: the value the host function returns. -/
def pairingCheck (data : ByteArray) : Except String Bool := do
  if data.size % 192 != 0 then
    throw "length is not a multiple of 192"
  let mut pairs := #[]
  for i in [0:data.size / 192] do
    let some a := decodeG1 data (192 * i) | throw "invalid g1"
    let some q := decodeG2 ops data (192 * i + 64) | throw "invalid g2"
    pairs := pairs.push (a, q)
  pure (ops.pairingCheck pairs.toList)

end Host

/-! ### The reference operations -/

namespace Spec

def f1 : Fld Nat :=
  fpFld p

def f2 : Fld Fp2 :=
  fp2Fld p

def g1Sum (terms : List (Bool × G1)) : G1 :=
  Jac.toAffine f1 <|
    terms.foldl
      (fun acc (neg, pt) =>
        let j := Jac.ofAffine f1 pt
        Jac.add f1 acc (if neg then Jac.neg f1 j else j))
      (Jac.inf f1)

def g1Multiexp (terms : List (G1 × Nat)) : G1 :=
  Jac.toAffine f1 <|
    terms.foldl (fun acc (pt, k) => Jac.add f1 acc (Jac.mul f1 (Jac.ofAffine f1 pt) k)) (Jac.inf f1)

def inG2 (q : Fp2 × Fp2) : Bool :=
  Jac.isInf f2 (Jac.mul f2 (Jac.ofAffine f2 (some q)) r)

def pairingCheck (pairs : List (G1 × G2)) : Bool :=
  Pairing.Spec.pairingCheck curve pairs

/-- The reference operations. -/
def ops : Ops :=
  { g1Sum, g1Multiexp, inG2, pairingCheck }

end Spec

namespace Impl

/-- The fast pairing's constants (`x = 4965661367192848881`). -/
def params : Params :=
  Params.ofCurve curve 4965661367192848881

def pairingCheck (pairs : List (G1 × G2)) : Bool :=
  Pairing.Impl.pairingCheck params pairs

def f1 : Fld Nat :=
  Spec.f1

def f2 : Fld Fp2 :=
  Spec.f2

/-- The sum, term by term in Jacobian coordinates. -/
def g1Sum (terms : List (Bool × G1)) : G1 :=
  Spec.g1Sum terms

/-- `∑ kᵢ Pᵢ`: one chain of doublings, windowed multiples of each point. -/
def g1Multiexp (terms : List (G1 × Nat)) : G1 :=
  Jac.toAffine f1 <| Jac.multiScalar f1 (terms.toArray.map fun (pt, k) => (Jac.ofAffine f1 pt, k))

/-- A point `Q` of the twist is in the subgroup of order `r` exactly when `ψ(Q) = [6 x²] Q` for the
Frobenius `ψ` of the twist: `ψ² - t ψ + p = 0` with the trace `t = 6 x² + 1` makes
`deg ([6 x²] - ψ) = 36 x⁴ + p - 6 x² t = r`, so the kernel of `[6 x²] - ψ` has `r` points and is
the subgroup. -/
def inG2 (q : Fp2 × Fp2) : Bool :=
  let psi := (Fp2.mul p (Fp2.conj p q.1) params.twX, Fp2.mul p (Fp2.conj p q.2) params.twY)
  Jac.eqAffine f2 (Jac.mul f2 (Jac.ofAffine f2 (some q)) (6 * 4965661367192848881 ^ 2)) psi.1 psi.2

/-- The fast operations. -/
def ops : Ops :=
  { g1Sum, g1Multiexp, inG2, pairingCheck }

end Impl

end NearCrypto.Bn254
