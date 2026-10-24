import NearCrypto.Pairing.Group

/-!
# P-256: the VM's `p256_verify`

`VMLogic::p256_verify` of `near-vm-runner` 0.37.4 (`logic/logic.rs`), over `p256` 0.13.2 and
`ecdsa` 0.16.9, in the order the host function checks things:

1. The signature must be 64 bytes (else an error of the VM). `Signature::from_slice` takes `r ‖ s`
   as two big-endian 32-byte numbers that must be in `[1, n - 1]`; otherwise the answer is **false**,
   before the key is even looked at.
2. The public key must be 33 bytes (else an error of the VM). `VerifyingKey::from_sec1_bytes` takes
   a compressed point: tag 02 or 03 and `x < p` with `x³ - 3 x + b` a square, `y` of the tag's parity.
   Any other tag (04 at this length, 00, …), `x ≥ p` or a non-square gives **false**.
3. The message is the **digest itself** (`verify_prehash`): fewer than 16 bytes give false; the
   leftmost 32 bytes are used when there are more, and a shorter digest is read as the number
   its bytes spell (left-padded with zeros). It is reduced modulo `n`.
4. `u₁ = z s⁻¹`, `u₂ = r s⁻¹` modulo `n`, `R = u₁ G + u₂ Q`; the answer is true when `R` is not
   the identity and its abscissa reduced modulo `n` is `r`. There is no low-`s` rule.

The functions return the host's value for well-formed lengths and `Except.error` for the two
length errors.
-/

namespace NearCrypto.P256

open NearCrypto.Pairing

/-- The field prime `2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`. -/
def p : Nat :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- The order of the group. -/
def n : Nat :=
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- `y² = x³ - 3 x + b`. -/
def b : Nat :=
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

def gx : Nat :=
  0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296

def gy : Nat :=
  0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- The base field as a record, with `a = -3`. -/
def fld : Fld Nat :=
  { fpFld p with a := p - 3 }

/-- `y² = x³ - 3 x + b`. -/
def curveRhs (x : Nat) : Nat :=
  (x * x % p * x + (p - 3) * x + b) % p

/-- `VerifyingKey::from_sec1_bytes` for 33 bytes: a compressed point. -/
def parseKey (pk : ByteArray) : Option (Nat × Nat) :=
  let tag := pk.get! 0
  let x := beNat pk 1 32
  if (tag == 2 || tag == 3) && x < p then
    match sqrtMod p (curveRhs x) with
    | some y => some (x, if (y % 2 == 1) == (tag == 3) then y else p - y)
    | none => none
  else none

/-- `u₁ G + u₂ Q` as an affine point; `none` is the identity. -/
abbrev MulAdd :=
  Nat → (Nat × Nat) → Nat → Option (Nat × Nat)

/-- `p256_verify` over the given double multiplication. -/
def verifyWith (mulAdd : MulAdd) (sig msg pk : ByteArray) : Except String Bool := do
  if sig.size != 64 then
    throw "invalid signature length"
  let r := beNat sig 0 32
  let s := beNat sig 32 32
  if r == 0 || s == 0 || r ≥ n || s ≥ n then
    return false
  if pk.size != 33 then
    throw "invalid public key length"
  let some q := parseKey pk | return false
  if msg.size < 16 then
    return false
  let z := beNat msg 0 (min 32 msg.size) % n
  let sInv := invMod n s
  match mulAdd (z * sInv % n) q (r * sInv % n) with
  | none =>
    return false
  | some (x, _) =>
    return x % n == r

namespace Spec

/-- The reference double multiplication: two scalar multiplications and an addition. -/
def mulAdd : MulAdd := fun u1 q u2 =>
  Jac.toAffine fld <|
    Jac.add fld (Jac.mul fld (Jac.ofAffine fld (some (gx, gy))) u1)
      (Jac.mul fld (Jac.ofAffine fld (some q)) u2)

def verify :=
  verifyWith mulAdd

end Spec

namespace Impl

/-- The fast double multiplication: one chain of doublings shared by both scalars. -/
def mulAdd : MulAdd := fun u1 q u2 =>
  Jac.toAffine fld <|
    Jac.multiScalar fld #[(Jac.ofAffine fld (some (gx, gy)), u1), (Jac.ofAffine fld (some q), u2)]

def verify :=
  verifyWith mulAdd

end Impl

end NearCrypto.P256
