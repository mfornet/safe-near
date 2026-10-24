import NearCrypto.Sha512

/-!
# Ed25519, reference semantics

The signature scheme of RFC 8032 with the acceptance rules of `ed25519-dalek`
2.2.0 as `near-crypto` 0.37.4 calls it (`VerifyingKey::from_bytes` followed by
the non-strict `Verifier::verify`, without the `legacy_compatibility`
feature):

* the public key bytes decode by `curve25519-dalek` 4.1.3 `decompress`
  (`edwards.rs`): the sign bit is bit 255, `y` is the remaining 255 bits taken
  modulo `p` without a canonical check, `x² = (y² − 1) / (d y² + 1)` must have a
  root, and `x = 0` with the sign bit set is accepted (ZIP 215);
* `S` must be below the group order `ℓ` (`signature.rs`, `check_scalar`);
* the check is cofactorless: `compress([S]B − [k]A)` must equal the 32 bytes
  of `R` exactly, so a non-canonical `R` is rejected (`verifying.rs`,
  `raw_verify` and `RCompute`), while small-order and mixed-order keys are
  accepted when the equation holds;
* `k = SHA-512(R ‖ A ‖ M) mod ℓ`, where `A` is the key bytes as given.

Everything is over `Nat`, with the textbook unified addition law on projective
points (Bernstein, Birkner, Joye, Lange and Peters, "Twisted Edwards curves",
`add-2008-bbjlp`) and one Fermat inversion per encoding. It favours clarity
over speed; `NearCrypto.Ed25519.Impl` is the fast version.
-/

namespace NearCrypto.Ed25519.Spec

/-- The field prime `2²⁵⁵ − 19`. -/
def p : Nat :=
  2 ^ 255 - 19

/-- The order `ℓ` of the base point. -/
def ell : Nat :=
  2 ^ 252 + 27742317777372353535851937790883648493

/-- `a ^ e mod p` by square and multiply, over `fuel` bits of `e`. -/
def powMod (a e : Nat) : Nat :=
  (List.range 256).reverse.foldl
    (fun r i =>
      let r := r * r % p;
      if e.testBit i then r * a % p else r)
    1

/-- The inverse of `a` modulo `p` (zero for zero). -/
def inv (a : Nat) : Nat :=
  powMod a (p - 2)

/-- The curve constant `d = −121665 / 121666`. -/
def d : Nat :=
  (p - 121665) * inv 121666 % p

/-- A square root of `−1`. -/
def sqrtM1 : Nat :=
  powMod 2 ((p - 1) / 4)

/-- A projective point `(X : Y : Z)`, the affine point `(X / Z, Y / Z)` on
`−x² + y² = 1 + d x² y²`. -/
abbrev Point :=
  Nat × Nat × Nat

/-- The identity. -/
def zero : Point :=
  (0, 1, 1)

/-- The unified addition law of the twisted Edwards curve with `a = −1` (complete, since `d` is
not a square). -/
def add (P Q : Point) : Point :=
  let (x1, y1, z1) := P
  let (x2, y2, z2) := Q
  let a := z1 * z2 % p
  let b := a * a % p
  let c := x1 * x2 % p
  let e := y1 * y2 % p
  let f := d * c % p * e % p
  let g := (b + p - f) % p
  let h := (b + f) % p
  (a * g % p * ((x1 + y1) * (x2 + y2) % p + 2 * p - c - e) % p, a * h % p * ((e + c) % p) % p,
    g * h % p)

/-- The negative of a point. -/
def neg (P : Point) : Point :=
  ((p - P.1) % p, P.2)

/-- `n · P` by double and add, over the 256 low bits of `n`. -/
def mul (n : Nat) (P : Point) : Point :=
  (List.range 256).reverse.foldl
    (fun R i =>
      let R := add R R;
      if n.testBit i then add R P else R)
    zero

/-- A root `x` of `x² = u / v` when there is one. -/
def sqrtRatio (u v : Nat) : Option Nat :=
  let r := u * powMod v 3 % p * powMod (u * powMod v 7 % p) ((p - 5) / 8) % p
  let c := v * r % p * r % p
  if c = u % p then some r else if c = (p - u % p) % p then some (r * sqrtM1 % p) else none

/-- The base point: `y = 4/5` and the root `x` of even parity. -/
def basePoint : Point :=
  let y := 4 * inv 5 % p
  let x := (sqrtRatio ((y * y + p - 1) % p) ((d * y % p * y + 1) % p)).getD 0
  ((if x % 2 = 0 then x else p - x), y, 1)

/-- Little-endian integer value of bytes. -/
def toNat (b : ByteArray) : Nat :=
  b.toList.foldr (fun x n => n * 256 + x.toNat) 0

/-- The `n`-byte little-endian encoding of `x`. -/
def ofNat (n x : Nat) : ByteArray :=
  ⟨((List.range n).map fun i => UInt8.ofNat (x / 256 ^ i)).toArray⟩

/-- `curve25519-dalek` `CompressedEdwardsY::decompress`. -/
def decompress (b : ByteArray) : Option Point :=
  if b.size != 32 then none
  else
    let n := toNat b
    let y := n % 2 ^ 255 % p
    let sign := n / 2 ^ 255
    match sqrtRatio ((y * y + p - 1) % p) ((d * y % p * y + 1) % p) with
    | none => none
    | some x =>
      let x := x % p
      -- the root of even parity, then negated when the sign bit says so
      let x := if x % 2 = 0 then x else p - x
      some ((if sign = 1 then (p - x) % p else x), y, 1)

/-- The canonical 32-byte encoding. -/
def compress (P : Point) : ByteArray :=
  let zi := inv P.2.2
  let x := P.1 * zi % p
  let y := P.2.1 * zi % p
  ofNat 32 (y + 2 ^ 255 * (x % 2))

/-- `Scalar::from_bytes_mod_order_wide` of a 64-byte hash. -/
def reduce (h : ByteArray) : Nat :=
  toNat h % ell

/-- Whether the public key bytes decode (`VerifyingKey::from_bytes`). -/
def validPublicKey (pk : ByteArray) : Bool :=
  (decompress pk).isSome

/-- Verify as `near-crypto` does: `pk` 32 bytes, `sig` 64 bytes. -/
def verify (pk msg sig : ByteArray) : Bool :=
  if pk.size != 32 || sig.size != 64 then false
  else
    match decompress pk with
    | none => false
    | some A =>
      let rBytes := sig.extract 0 32
      let s := toNat (sig.extract 32 64)
      if s ≥ ell then false
      else
        let k := reduce (Sha512.Spec.hash (rBytes ++ pk ++ msg))
        let R := add (mul s basePoint) (mul k (neg A))
        compress R == rBytes

/-- The scalar and hash prefix of a seed: SHA-512, then the clamping of the low half. -/
def expand (seed : ByteArray) : Nat × ByteArray :=
  let h := Sha512.Spec.hash seed
  let a := toNat (h.extract 0 32)
  ((a % 2 ^ 254) / 8 * 8 + 2 ^ 254, h.extract 32 64)

/-- The public key of a 32-byte seed. -/
def publicKey (seed : ByteArray) : ByteArray :=
  compress (mul (expand seed).1 basePoint)

/-- `SigningKey::from_keypair_bytes`: the public half must be the one the seed derives. -/
def validKeypair (keypair : ByteArray) : Bool :=
  keypair.size == 64 && publicKey (keypair.extract 0 32) == keypair.extract 32 64

/-- Deterministic RFC 8032 signature of `msg` by the key of a 32-byte seed. -/
def sign (seed msg : ByteArray) : ByteArray :=
  let (a, prefix_) := expand seed
  let pk := publicKey seed
  let r := reduce (Sha512.Spec.hash (prefix_ ++ msg))
  let R := compress (mul r basePoint)
  let k := reduce (Sha512.Spec.hash (R ++ pk ++ msg))
  R ++ ofNat 32 ((r + k * a) % ell)

end NearCrypto.Ed25519.Spec
