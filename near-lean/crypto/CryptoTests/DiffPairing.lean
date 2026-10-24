import NearCrypto
import CryptoTests.Fixtures
import CryptoTests.Rng

/-!
Differential tests of the pairing code, for one curve at a time: the tower and its Frobenius
(`Pairing.Tower`) against the flat reference `Fp12` (`Pairing.Spec`), group operations, the
subgroup tests, and the fast reduced pairing against the reference one (equal, since the final
exponentiation removes the line scalings).
-/

namespace CryptoTests.DiffPairing

open NearCrypto NearCrypto.Pairing

/-- A curve to test: its parameters for both pairings and the generators. -/
structure Kit where
  name : String
  curve : Curve
  params : Params
  g1 : Nat × Nat
  g2 : Fp2 × Fp2

def chk (t : Tally) (name : String) (ok : Bool) (detail : String := "") : Tally :=
  t.record name (if ok then none else some detail)

/-- A random number below `m`. -/
def below (r : Rng) (m : Nat) : Nat × Rng :=
  let (b, r) := r.bytes (m.log2 / 8 + 9)
  (beNat b 0 b.size % m, r)

def randFp2 (r : Rng) (p : Nat) : Fp2 × Rng :=
  let (a, r) := below r p
  let (b, r) := below r p
  (⟨a, b⟩, r)

def randFp12 (r : Rng) (p : Nat) : Fp12 × Rng :=
  Id.run do
    let mut r := r
    let mut cs := #[]
    for _ in [0:6] do
      let (z, r') := randFp2 r p
      cs := cs.push z
      r := r'
    return (⟨⟨cs[0]!, cs[1]!, cs[2]!⟩, ⟨cs[3]!, cs[4]!, cs[5]!⟩⟩, r)

/-- The element of the tower in the flat `Fp12` of the reference: `∑ gᵢ wⁱ`. -/
def toFlat (c : Curve) (x : Fp12) : Spec.F12 :=
  let g := #[x.c0.c0, x.c1.c0, x.c0.c1, x.c1.c1, x.c0.c2, x.c1.c2]
  (List.range 6).foldl (fun acc i => Spec.add c acc (Spec.mul c (Spec.ofFp2 c g[i]!) (Spec.wPow i)))
    (Spec.ofFp 0)

/-- A point of the group `G1` or the twist from a scalar. -/
def mulG1 (K : Kit) (k : Nat) : Option (Nat × Nat) :=
  let F := fpFld K.curve.p
  Jac.toAffine F (Jac.mul F (Jac.ofAffine F (some K.g1)) k)

def mulG2 (K : Kit) (k : Nat) : Option (Fp2 × Fp2) :=
  let F := fp2Fld K.curve.p
  Jac.toAffine F (Jac.mul F (Jac.ofAffine F (some K.g2)) k)

/-- A point of the twist, found by abscissa: on the curve and, in general, outside the subgroup. -/
def randTwist (K : Kit) (r : Rng) : (Fp2 × Fp2) × Rng :=
  Id.run do
    let c := K.curve
    let mut r := r
    for _ in [0:200] do
      let (x, r') := randFp2 r c.p
      r := r'
      let rhs := Fp2.add c.p (Fp2.mul c.p (Fp2.sqr c.p x) x) c.b2
      match Fp2.sqrt c.p rhs with
      | some y =>
        return ((x, y), r)
      | none =>
        pure ()
    return (K.g2, r)

def tests (K : Kit) (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let c := K.curve
    let ctx := K.params.ctx
    let mut t := t
    let mut r := r
    let n := K.name
    -- the tower against the flat field
    for i in [0:6] do
      let (a, r1) := randFp12 r c.p
      let (b, r2) := randFp12 r1 c.p
      r := r2
      t :=
        chk t s!"{n} tower mul {i}"
          (toFlat c (Fp12.mul ctx a b) == Spec.mul c (toFlat c a) (toFlat c b))
      t :=
        chk t s!"{n} tower sqr {i}"
          (toFlat c (Fp12.sqr ctx a) == Spec.mul c (toFlat c a) (toFlat c a))
      t := chk t s!"{n} tower inv {i}" (Fp12.mul ctx a (Fp12.inv ctx a) == Fp12.one)
      t := chk t s!"{n} tower frob {i}" (toFlat c (Fp12.frob ctx a) == Spec.pow c (toFlat c a) c.p)
      t :=
        chk t s!"{n} tower frob2 {i}"
          (toFlat c (Fp12.frob2 ctx a) == Spec.pow c (toFlat c a) (c.p ^ 2))
      t :=
        chk t s!"{n} tower conj {i}"
          (toFlat c (Fp12.conj ctx a) == Spec.pow c (toFlat c a) (c.p ^ 6))
      let (z, r3) := randFp2 r c.p
      r := r3
      t := chk t s!"{n} fp2 inv {i}" (Fp2.isZero z || Fp2.mul c.p z (Fp2.inv c.p z) == Fp2.one)
      t :=
        chk t s!"{n} fp2 sqrt {i}"
          (match Fp2.sqrt c.p (Fp2.sqr c.p z) with
          | some s => Fp2.sqr c.p s == Fp2.sqr c.p z
          | none => false)
    -- the generators are in the groups
    t := chk t s!"{n} g1 order" (mulG1 K c.r == none && mulG1 K 1 == some K.g1)
    t := chk t s!"{n} g2 order" (mulG2 K c.r == none && mulG2 K 1 == some K.g2)
    t := chk t s!"{n} g2 on twist" (Spec.twOnCurve c (some K.g2))
    -- the reduced pairing: fast equals reference, and it is bilinear
    for i in [0:3] do
      let (a, r1) := below r c.r
      let (b, r2) := below r1 c.r
      r := r2
      match mulG1 K a, mulG2 K b with
      | some pa, some qb =>
        let fast := Impl.finalExp K.params (Impl.millerLoop K.params #[(pa, qb)])
        let slow := Spec.finalExp c (Spec.miller c qb pa)
        t := chk t s!"{n} pairing fast = reference {i}" (toFlat c fast == slow)
        let e1 := Impl.finalExp K.params (Impl.millerLoop K.params #[(K.g1, K.g2)])
        let eab := Impl.finalExp K.params (Impl.millerLoop K.params #[(pa, qb)])
        t := chk t s!"{n} pairing bilinear {i}" (eab == Fp12.pow ctx e1 (a * b % c.r))
      | _, _ =>
        t := chk t s!"{n} scalar {i}" false
    return (t, r)

def bn254Kit : Kit :=
  { name := "bn254", curve := Bn254.curve, params := Bn254.Impl.params, g1 := (1, 2),
    g2 :=
      (⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
          11559732032986387107991004021392285783925812861821192530917403151452391805634⟩,
        ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
          4082367875863433681332203403145435568316851327593401208105741076214120093531⟩) }

/-- BN254 host-level operations: the fast ones against the reference ones. -/
def bnOpsTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let K := bn254Kit
    let mut t := t
    let mut r := r
    -- sums and multi-exponentiations, with zero scalars, infinity and repeated points
    for i in [0:12] do
      let mut terms : List (Option (Nat × Nat) × Nat) := []
      let mut sgn : List (Bool × Option (Nat × Nat)) := []
      let (cnt, r1) := below r 9
      r := r1
      for j in [0:cnt] do
        let (k, r1) := below r Bn254.r
        let (m, r2) := below r1 5
        r := r2
        let pt := if m == 0 then none else if m == 1 && j > 0 then some K.g1 else mulG1 K k
        let (kk, r3) := below r (if m == 2 then 3 else Bn254.r)
        r := r3
        terms := terms ++ [(pt, kk)]
        sgn := sgn ++ [(k % 3 == 0, pt)]
      t := chk t s!"bn254 multiexp {i}" (Bn254.Impl.g1Multiexp terms == Bn254.Spec.g1Multiexp terms)
      t := chk t s!"bn254 sum {i}" (Bn254.Impl.g1Sum sgn == Bn254.Spec.g1Sum sgn)
    -- the subgroup test on points of the twist: the fast one is the reference one
    for i in [0:6] do
      let (q, r1) := randTwist K r
      r := r1
      t := chk t s!"bn254 inG2 {i}" (Bn254.Impl.inG2 q == Bn254.Spec.inG2 q)
      let (k, r2) := below r Bn254.r
      r := r2
      match mulG2 K k with
      | some q' =>
        t := chk t s!"bn254 inG2 member {i}" (Bn254.Impl.inG2 q' && Bn254.Spec.inG2 q')
        -- a member plus a point of the cofactor part is outside, whatever the cofactor part is
        let F := fp2Fld Bn254.p
        let mixed := Jac.toAffine F (Jac.add F (Jac.ofAffine F (some q')) (Jac.ofAffine F (some q)))
        match mixed with
        | some m =>
          t := chk t s!"bn254 inG2 mixed {i}" (Bn254.Impl.inG2 m == Bn254.Spec.inG2 m)
        | none =>
          pure ()
      | none =>
        pure ()
    return (t, r)

end CryptoTests.DiffPairing
