import NearCrypto.Hmac

/-!
# secp256k1 ECDSA, reference semantics

The curve `y² = x³ + 7` over `GF(p)` with the group of prime order `n`, and the ECDSA operations
exactly as `near-crypto` 0.37.4 reaches them through `secp256k1` 0.27.0, that is through the
`libsecp256k1` C sources vendored in `secp256k1-sys` 0.8.2:

* **Public keys** (`secp256k1_eckey_pubkey_parse`, `eckey_impl.h`): 33 bytes with tag `02`/`03` and
  an `x < p` that is the abscissa of a point (`secp256k1_ge_set_xo_var`: `x³ + 7` has a root, and
  the root of the stated parity is taken), or 65 bytes with tag `04`, `06` or `07` where `x, y < p`,
  the point is on the curve and, for `06`/`07`, the parity of `y` is the tag's. Nothing else parses.
  `near-crypto` stores the 64 bytes `x ‖ y` and prefixes `04`.
* **Scalars** (`scalar_set_b32`): a 32-byte big-endian number reduced modulo `n`, and an overflow
  flag when it was `≥ n`. A secret key or a nonce is valid when it did not overflow and is not zero.
* **Recovery** (`secp256k1_ecdsa_sig_recover`, `recovery/main_impl.h`): the signature parses only
  when `r, s < n` and the recovery id is 0 to 3; `r = 0` or `s = 0` recovers nothing. For ids 2 and 3
  `r ≥ p − n` recovers nothing and the abscissa is `r + n`; the point `R` has the abscissa and, as
  its parity, bit 0 of the id (no root: nothing recovered). `Q = r⁻¹ (s R − m G)` with the message
  `m` reduced modulo `n`; the point at infinity recovers nothing.
* **Verification** (`secp256k1_ecdsa_verify`, `secp256k1.c`; `near-crypto` `Signature::verify`): the
  message must be 32 bytes, the recovery id 0 to 3 (and otherwise unused), `r, s < n` and
  **`s` not high** (`s ≤ (n − 1) / 2`), `r, s ≠ 0`, and the `x` coordinate of `s⁻¹ m G + s⁻¹ r Q`
  taken modulo `n` equals `r`.
* **Signing** (`secp256k1_ecdsa_sign_recoverable` with `secp256k1_nonce_function_rfc6979`, no extra
  data): the nonce of attempt `c` is the `c + 1`-st output of the HMAC-SHA256 DRBG seeded with
  `seckey ‖ (m mod n)`; invalid nonces and a zero `r` or `s` retry; `s` is made low and bit 0 of the
  recovery id flips with it; bit 1 is the overflow of `R.x` over `n`.
* **`ecrecover` host function** (`near-vm-runner` 0.37.4, `logic.rs`): `r < n`, `s < n` (and
  `s ≤ (n − 1) / 2` with the malleability flag) are checked first, then the recovery above; the key
  is returned as 64 bytes. The length and range checks of the arguments are errors of the VM.

All arithmetic is over `Nat`, in Jacobian coordinates with one inversion per result. It favours
clarity over speed; `NearCrypto.Secp256k1.Impl` is the fast version.
-/

namespace NearCrypto.Secp256k1.Spec

/-- The field prime `2²⁵⁶ − 2³² − 977`. -/
def p : Nat :=
  2 ^ 256 - 2 ^ 32 - 977

/-- The order of the group. -/
def n : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- The base point. -/
def gx : Nat :=
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798

/-- The base point. -/
def gy : Nat :=
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

/-- `a ^ e mod m` by square and multiply over the 256 low bits of `e`. -/
def powMod (m a e : Nat) : Nat :=
  (List.range 256).reverse.foldl
    (fun r i =>
      let r := r * r % m;
      if e.testBit i then r * a % m else r)
    1

/-- The inverse modulo the prime `m` (zero for zero). -/
def inv (m a : Nat) : Nat :=
  powMod m a (m - 2)

/-- A root of `a` modulo `p` when there is one (`p ≡ 3 mod 4`). -/
def sqrt (a : Nat) : Option Nat :=
  let y := powMod p a ((p + 1) / 4)
  if y * y % p = a % p then some y else none

/-- A point as an affine pair; `none` is the point at infinity. -/
abbrev Point :=
  Option (Nat × Nat)

/-- A Jacobian point `(X : Y : Z)`, the affine `(X / Z², Y / Z³)`; `Z = 0` is infinity. -/
abbrev Jac :=
  Nat × Nat × Nat

/-- Whether `(x, y)` is on the curve. -/
def onCurve (x y : Nat) : Bool :=
  y * y % p == (x * x % p * x + 7) % p

/-- The Jacobian form of a point. -/
def ofPoint : Point → Jac
  | none => (1, 1, 0)
  | some (x, y) => (x, y, 1)

/-- Doubling (`dbl-2009-l`). -/
def dbl (P : Jac) : Jac :=
  let (x, y, z) := P
  if z = 0 || y = 0 then (1, 1, 0)
  else
    let a := x * x % p
    let b := y * y % p
    let c := b * b % p
    let d := 2 * (((x + b) * (x + b) % p + 2 * p - a - c) % p) % p
    let e := 3 * a % p
    let f := e * e % p
    let x3 := (f + 2 * p - 2 * d) % p
    (x3, (e * ((d + p - x3) % p) + 8 * (p - c)) % p, 2 * y * z % p)

/-- Addition (`add-2007-bl`, with the special cases). -/
def add (P Q : Jac) : Jac :=
  let (x1, y1, z1) := P
  let (x2, y2, z2) := Q
  if z1 = 0 then Q
  else
    if z2 = 0 then P
    else
      let z1z1 := z1 * z1 % p
      let z2z2 := z2 * z2 % p
      let u1 := x1 * z2z2 % p
      let u2 := x2 * z1z1 % p
      let s1 := y1 * z2 % p * z2z2 % p
      let s2 := y2 * z1 % p * z1z1 % p
      if u1 = u2 then if s1 = s2 then dbl P else (1, 1, 0)
      else
        let h := (u2 + p - u1) % p
        let r := (s2 + p - s1) % p
        let hh := h * h % p
        let hhh := hh * h % p
        let v := u1 * hh % p
        let x3 := (r * r + 4 * p - hhh - 2 * v) % p
        (x3, (r * ((v + p - x3) % p) + (p - s1) * hhh) % p, z1 * z2 % p * h % p)

/-- The negative of a Jacobian point. -/
def neg (P : Jac) : Jac :=
  (P.1, (p - P.2.1) % p, P.2.2)

/-- `a · P + b · Q` by one shared double and add chain over the 257 low bits. -/
def mulJ2 (a : Nat) (P : Jac) (b : Nat) (Q : Jac) : Jac :=
  let PQ := add P Q
  (List.range 257).reverse.foldl
    (fun R i =>
      let R := dbl R
      match a.testBit i, b.testBit i with
      | true, true => add R PQ
      | true, false => add R P
      | false, true => add R Q
      | false, false => R)
    (1, 1, 0)

/-- The affine point of a Jacobian one. -/
def toPoint (P : Jac) : Point :=
  if P.2.2 = 0 then none
  else
    let zi := inv p P.2.2
    some (P.1 * zi % p * zi % p, P.2.1 * zi % p * zi % p * zi % p)

/-- The base point as a point. -/
def basePoint : Point :=
  some (gx, gy)

/-- `a · P + b · G`. -/
def ecmult (a : Nat) (P : Point) (b : Nat) : Point :=
  toPoint (mulJ2 a (ofPoint P) b (ofPoint basePoint))

/-! ### Bytes and scalars -/

/-- The big-endian value of bytes. -/
def toNat (b : ByteArray) : Nat :=
  b.foldl (fun x c => x * 256 + c.toNat) 0

/-- The `len`-byte big-endian encoding of `x`. -/
def ofNat (len x : Nat) : ByteArray :=
  ⟨((List.range len).reverse.map fun i => UInt8.ofNat (x / 256 ^ i)).toArray⟩

/-- `n / 2 + 1`: a signature scalar below it is low (`near-crypto`'s `SECP256K1_N_HALF_ONE`). -/
def nHalfOne : Nat :=
  n / 2 + 1

/-- A secret key or nonce: 32 bytes, not zero and below `n` (`secp256k1_ec_seckey_verify`). -/
def validSecret (b : ByteArray) : Bool :=
  b.size == 32 && 0 < toNat b && toNat b < n

/-! ### Public keys -/

/-- `secp256k1_eckey_pubkey_parse`. -/
def parsePublicKey (b : ByteArray) : Option (Nat × Nat) :=
  let tag := b.data.getD 0 0
  if b.size == 33 && (tag == 2 || tag == 3) then
    let x := toNat (b.extract 1 33)
    if x < p then
      match sqrt ((x * x % p * x + 7) % p) with
      | none => none
      | some y => some (x, if (y % 2 == 1) == (tag == 3) then y else (p - y) % p)
    else none
  else
    if b.size == 65 && (tag == 4 || tag == 6 || tag == 7) then
      let x := toNat (b.extract 1 33)
      let y := toNat (b.extract 33 65)
      if x < p && y < p && (tag == 4 || (y % 2 == 1) == (tag == 7)) && onCurve x y then some (x, y)
      else none
    else none

/-- The 65-byte form with tag `04`. -/
def serializeUncompressed (x y : Nat) : ByteArray :=
  (ByteArray.empty.push 4) ++ ofNat 32 x ++ ofNat 32 y

/-- The 33-byte form. -/
def serializeCompressed (x y : Nat) : ByteArray :=
  (ByteArray.empty.push (if y % 2 == 1 then 3 else 2)) ++ ofNat 32 x

/-- The 64 bytes `x ‖ y` that `near-crypto` stores. -/
def serializeRaw (x y : Nat) : ByteArray :=
  ofNat 32 x ++ ofNat 32 y

/-- The public key of a valid secret key as `(x, y)`. -/
def publicKey (sk : ByteArray) : Option (Nat × Nat) :=
  if validSecret sk then (ecmult 0 none (toNat sk)) else none

/-! ### Recovery and verification -/

/-- `secp256k1_ecdsa_sig_recover`: `m` is the message already reduced modulo `n`. -/
def recover (r s recid m : Nat) : Point :=
  if r = 0 || s = 0 then none
  else
    if recid ≥ 2 && r ≥ p - n then none
    else
      let x := if recid ≥ 2 then r + n else r
      match sqrt ((x * x % p * x + 7) % p) with
      | none => none
      | some y =>
        let y := if y % 2 == recid % 2 then y else (p - y) % p
        let rn := inv n r
        ecmult (rn * s % n) (some (x, y)) ((n - rn * m % n) % n)

/-- `secp256k1_ecdsa_verify` for the scalars `r`, `s`, the reduced message `m` and the key. -/
def verifyScalars (r s m : Nat) (pk : Nat × Nat) : Bool :=
  if r = 0 || s = 0 || s ≥ nHalfOne then false
  else
    let sn := inv n s
    match ecmult (sn * r % n) (some pk) (sn * m % n) with
    | none => false
    | some (x, _) => x % n == r

/-- `near_crypto::Signature::verify` for SECP256K1: the 64-byte key, the message, the 65-byte
signature `r ‖ s ‖ v`. -/
def verify (pk msg sig : ByteArray) : Bool :=
  if pk.size != 64 || sig.size != 65 || msg.size != 32 || sig.get! 64 ≥ 4 then false
  else
    let r := toNat (sig.extract 0 32)
    let s := toNat (sig.extract 32 64)
    if r ≥ n || s ≥ n then false
    else
      match parsePublicKey ((ByteArray.empty.push 4) ++ pk) with
      | none => false
      | some q => verifyScalars r s (toNat msg % n) q

/-- `near_crypto::Secp256K1Signature::recover` with the checks of `from_compact`: the 64-byte
public key of a signature `r ‖ s ‖ v` over a 32-byte message. -/
def recoverKey (msg sig : ByteArray) : Option ByteArray :=
  if msg.size != 32 || sig.size != 65 || sig.get! 64 ≥ 4 then none
  else
    let r := toNat (sig.extract 0 32)
    let s := toNat (sig.extract 32 64)
    if r ≥ n || s ≥ n then none
    else (recover r s (sig.get! 64).toNat (toNat msg % n)).map fun (x, y) => serializeRaw x y

/-- The VM host function `ecrecover(hash, sig, v, malleability)` once the VM has checked the
argument lengths, `v < 4` and the flag: the 64-byte key, or `none` for a signature that is not
valid. -/
def ecrecover (hash sig : ByteArray) (v : Nat) (malleability : Bool) : Option ByteArray :=
  if hash.size != 32 || sig.size != 64 || v ≥ 4 then none
  else
    let r := toNat (sig.extract 0 32)
    let s := toNat (sig.extract 32 64)
    if r ≥ n || s ≥ (if malleability then nHalfOne else n) then none
    else (recover r s v (toNat hash % n)).map fun (x, y) => serializeRaw x y

/-! ### Signing -/

/-- The state of `secp256k1_rfc6979_hmac_sha256`: key, value and whether an output was drawn. -/
structure Drbg where
  k : ByteArray
  v : ByteArray
  retry : Bool

/-- Seed with `key = seckey ‖ reduced message` (RFC 6979 3.2 b to f). -/
def Drbg.init (key : ByteArray) : Drbg :=
  let v := ByteArray.mk (Array.replicate 32 1)
  let k := zeros 32
  let k := Hmac.Spec.sha256 k (v ++ (ByteArray.empty.push 0) ++ key)
  let v := Hmac.Spec.sha256 k v
  let k := Hmac.Spec.sha256 k (v ++ (ByteArray.empty.push 1) ++ key)
  { k, v := Hmac.Spec.sha256 k v, retry := false }

/-- The next 32 bytes (RFC 6979 3.2 h). -/
def Drbg.generate (d : Drbg) : ByteArray × Drbg :=
  let (k, v) :=
    if d.retry then
      let k := Hmac.Spec.sha256 d.k (d.v ++ (ByteArray.empty.push 0))
      (k, Hmac.Spec.sha256 k d.v)
    else (d.k, d.v)
  let v := Hmac.Spec.sha256 k v
  (v, { k, v, retry := true })

/-- `secp256k1_nonce_function_rfc6979`: the nonce of attempt `counter`. -/
def nonce (key32 msg32 : ByteArray) (counter : Nat) : ByteArray :=
  let m := ofNat 32 (toNat msg32 % n)
  ((List.range (counter + 1)).foldl (fun (_, d) _ => d.generate)
      (ByteArray.empty, Drbg.init (key32 ++ m))).1

/-- `secp256k1_ecdsa_sign_recoverable`: the 65 bytes `r ‖ s ‖ v` of a valid secret key and a
32-byte message, or `none`. -/
def signRecoverable (sk msg : ByteArray) : Option ByteArray :=
  if !validSecret sk || msg.size != 32 then none
  else
    let d := toNat sk
    let m := toNat msg % n
    let attempt (count : Nat) : Option ByteArray :=
      let k := toNat (nonce sk msg count)
      if k = 0 || k ≥ n then none
      else
        match ecmult 0 none k with
        | none => none
        | some (rx, ry) =>
          let r := rx % n
          let s := inv n k * ((m + r * d) % n) % n
          let high := s ≥ nHalfOne
          let s := if high then n - s else s
          let recid := (if rx ≥ n then 2 else 0) + (if (ry % 2 == 1) != high then 1 else 0)
          if r = 0 || s = 0 then none
          else some (ofNat 32 r ++ ofNat 32 s ++ (ByteArray.empty.push recid.toUInt8))
    -- an invalid nonce, a zero `r` or a zero `s` is retried with the next counter
    (List.range 64).findSome? attempt

end NearCrypto.Secp256k1.Spec
