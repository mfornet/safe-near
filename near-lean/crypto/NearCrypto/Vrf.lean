import NearCrypto.Blake2b
import NearCrypto.Ristretto
import NearCrypto.Sha256
import NearCrypto.Ed25519

/-!
# The NEAR VRF

`near-crypto` 0.37.4 `vrf.rs`, over ristretto255. A secret key is a canonical scalar `sk` and its
public key the encoding of `sk · B`. With `offset(pk, input) = H256(pk ‖ input)` (BLAKE2b-256 read
as a little-endian number modulo `ℓ`), the value of `input` is `enc(B / (sk + offset))`
(`1 / 0` is taken as `1`) and the proof is `(r, c)` with `x = sk + offset`, `inv = 1 / x`,
`k = H512(x)` (BLAKE2b-512 of the 32-byte scalar, reduced modulo `ℓ`), `c = H256(pk ‖ value ‖ enc(k B) ‖
enc(inv k B))` and `r = k - c x`, as the 64 bytes `r ‖ c`. Verification decodes the value, requires
`r` and `c` canonical, and checks that `c = H256(pk ‖ value ‖ enc((r + c offset) B + c pk) ‖ enc(r value + c B))`.

The block producer's VRF key is the ristretto form of its ed25519 key
(`key_conversion::convert_public_key`: the point must decompress as an Edwards point and be
torsion free) and its secret scalar the clamped scalar of the seed reduced modulo `ℓ`
(`convert_secret_key`). nearcore (`chain/chain/src/signature_verification.rs`, `verify_block_vrf`)
checks the VRF of each block over the previous block's `random_value`, and the block header's
`random_value` must be the SHA-256 of the VRF value.

`Spec` is `Nat` over the reference edwards25519 and ristretto255; `Impl` uses the ten-limb field.
-/

namespace NearCrypto.Vrf

/-- `a ^ e mod m` by square and multiply over the 256 low bits of `e`. -/
def powMod (m a e : Nat) : Nat :=
  (List.range 256).reverse.foldl
    (fun r i =>
      let r := r * r % m;
      if e.testBit i then r * a % m else r)
    1

/-! ### Spec -/

namespace Spec

open Ed25519.Spec

/-- BLAKE2b-256 of the concatenation as a scalar (`hash_s!`). -/
def hashS (parts : List ByteArray) : Nat :=
  toNat (Blake2b.Spec.hash 32 (parts.foldl (· ++ ·) ByteArray.empty)) % ell

/-- `prs!`: BLAKE2b-512 as a wide scalar. -/
def prs (x : ByteArray) : Nat :=
  reduce (Blake2b.Spec.hash 64 x)

/-- A canonical scalar (`Scalar::from_canonical_bytes`). -/
def canonical (b : ByteArray) : Option Nat :=
  if b.size == 32 && toNat b < ell then some (toNat b) else none

/-- `basemul` and `pack`. -/
def basemul (s : Nat) : ByteArray :=
  Ristretto.Spec.compress (mul s basePoint)

/-- `vmul2` and `pack`: `s1 P1 + s2 P2`. -/
def vmul2 (s1 : Nat) (P1 : Point) (s2 : Nat) (P2 : Point) : ByteArray :=
  Ristretto.Spec.compress (add (mul s1 P1) (mul s2 P2))

/-- `safe_invert`: the inverse modulo `ℓ`, and `1` for zero. -/
def safeInvert (s : Nat) : Nat :=
  if s % ell == 0 then 1 else powMod ell s (ell - 2)

/-- The public key of a secret scalar. -/
def publicKey (sk : Nat) : ByteArray :=
  basemul sk

/-- `PublicKey::offset`. -/
def offset (pk input : ByteArray) : Nat :=
  hashS [pk, input]

/-- `compute_vrf_with_proof`: the value and the proof of `input`. -/
def computeWithProof (sk : Nat) (input : ByteArray) : ByteArray × ByteArray :=
  let pk := publicKey sk
  let x := (sk + offset pk input) % ell
  let inv := safeInvert x
  let val := basemul inv
  let k := prs (ofNat 32 x)
  let c := hashS [pk, val, basemul k, basemul (inv * k % ell)]
  (val, ofNat 32 ((k + ell - c * x % ell) % ell) ++ ofNat 32 c)

/-- `is_vrf_valid`: whether `value` and `proof` are the VRF of `input` under the public key `pk`
(`false` when `pk` does not decode, a key `near-crypto` cannot construct). -/
def isValid (pk input value proof : ByteArray) : Bool :=
  match Ristretto.Spec.decompress pk, Ristretto.Spec.decompress value,
    canonical (proof.extract 0 32), canonical (proof.extract 32 64) with
  | some pkPoint, some p, some r, some c =>
    proof.size == 64 && pk.size == 32 && value.size == 32 &&
      hashS
          [pk, value, vmul2 ((r + c * offset pk input) % ell) basePoint c pkPoint,
            vmul2 r p c basePoint] ==
        c
  | _, _, _, _ => false

/-- `key_conversion::convert_public_key`: the ristretto form of an ed25519 public key that is a
torsion-free point. -/
def convertPublicKey (ed : ByteArray) : Option ByteArray :=
  match decompress ed with
  | some P =>
    if compress (mul ell P) == compress zero then some (Ristretto.Spec.compress P) else none
  | none => none

/-- `key_conversion::convert_secret_key`: the scalar of an ed25519 seed. -/
def convertSecretKey (seed : ByteArray) : Nat :=
  (expand seed).1 % ell

end Spec

/-! ### Impl -/

namespace Impl

open Ed25519

/-- BLAKE2b-256 of the concatenation as a scalar (`hash_s!`). -/
def hashS (parts : List ByteArray) : Nat :=
  Scalar.ofBytes (Blake2b.Impl.hash 32 (parts.foldl (· ++ ·) ByteArray.empty)) 0 4 % ell

/-- A canonical scalar (`Scalar::from_canonical_bytes`) at byte offset `off` of `b`. -/
def canonical (b : ByteArray) (off : Nat) : Option Nat :=
  let s := Scalar.ofBytes b off 4
  if off + 32 ≤ b.size && s < ell then some s else none

/-- The encoding of `s · B`. -/
def basemul (s : Nat) : ByteArray :=
  Ristretto.Impl.compress (Ext.mulBase s)

/-- The inverse modulo `ℓ`, and `1` for zero (`safe_invert`), by the extended Euclidean algorithm. -/
def safeInvert (s : Nat) : Nat :=
  if s % ell == 0 then 1
  else
    let rec go : Nat → Nat → Nat → Int → Int → Nat
      | 0, _, _, _, _ => 0
      | fuel + 1, r0, r1, t0, t1 =>
        if r1 == 0 then (t0 % (ell : Int)).toNat
        else
          let q := r0 / r1
          go fuel r1 (r0 - q * r1) t1 (t0 - (q : Int) * t1)
    go 600 ell (s % ell) 0 1

/-- A VRF secret key: a canonical scalar and its public key. -/
structure SecretKey where
  scalar : Nat
  publicKey : ByteArray

/-- `SecretKey::try_from(&[u8; 32])`: a canonical scalar. -/
def SecretKey.ofBytes (b : ByteArray) : Option SecretKey :=
  (canonical b 0).map fun s => ⟨s, basemul s⟩

/-- The scalar. -/
def SecretKey.toBytes (k : SecretKey) : ByteArray :=
  Scalar.toBytes32 k.scalar

/-- `convert_secret_key`: the VRF key of an ed25519 seed (32 bytes). -/
def SecretKey.ofSeed (seed : ByteArray) : Option SecretKey :=
  (Ed25519.Impl.SigningKey.ofSeed seed).map fun k => ⟨k.scalar % ell, basemul (k.scalar % ell)⟩

/-- `PublicKey::offset`. -/
def offset (pk input : ByteArray) : Nat :=
  hashS [pk, input]

/-- `compute_vrf_with_proof`: the 32-byte value and the 64-byte proof of `input`. -/
def SecretKey.computeWithProof (k : SecretKey) (input : ByteArray) : ByteArray × ByteArray :=
  let x := (k.scalar + offset k.publicKey input) % ell
  let inv := safeInvert x
  let val := basemul inv
  let nonce := Scalar.reduceWide (Blake2b.Impl.hash 64 (Scalar.toBytes32 x))
  let c := hashS [k.publicKey, val, basemul nonce, basemul (inv * nonce % ell)]
  (val, Scalar.toBytes32 ((nonce + ell - c * x % ell) % ell) ++ Scalar.toBytes32 c)

/-- `compute_vrf`: the value only. -/
def SecretKey.compute (k : SecretKey) (input : ByteArray) : ByteArray :=
  basemul (safeInvert ((k.scalar + offset k.publicKey input) % ell))

/-- `is_vrf_valid`: whether `value` and `proof` are the VRF of `input` under the public key `pk`
(`false` when `pk` does not decode, a key `near-crypto` cannot construct). -/
def isValid (pk input value proof : ByteArray) : Bool :=
  if pk.size != 32 || value.size != 32 || proof.size != 64 then false
  else
    match Ristretto.Impl.decompress pk, Ristretto.Impl.decompress value, canonical proof 0,
      canonical proof 32 with
    | some pkPoint, some p, some r, some c =>
      let u :=
        Ristretto.Impl.compress
          (Ext.doubleMul ((r + c * offset pk input) % ell) Ext.basePoint c pkPoint)
      let w := Ristretto.Impl.compress (Ext.doubleMul r p c Ext.basePoint)
      hashS [pk, value, u, w] == c
    | _, _, _, _ => false

/-- `key_conversion::convert_public_key`: the 32-byte ristretto form of an ed25519 public key
that is a torsion-free point, `none` otherwise. -/
def convertPublicKey (ed : ByteArray) : Option ByteArray :=
  match Ext.decompress ed with
  | some P =>
    if (Ext.doubleMul ell P 0 Ext.identity).isIdentity then some (Ristretto.Impl.compress P)
    else none
  | none => none

/-- `verify_block_vrf` of nearcore: the VRF check of a block over the previous block's random
value, under the producer's ed25519 key (`false` when the key does not convert, where nearcore
unwraps). -/
def blockVrfValid (producerKey prevRandom value proof : ByteArray) : Bool :=
  match convertPublicKey producerKey with
  | some pk => isValid pk prevRandom value proof
  | none => false

/-- The `random_value` of a block header: the SHA-256 of the VRF value. -/
def randomValue (value : ByteArray) : ByteArray :=
  Sha256.Impl.hash value

end Impl

end NearCrypto.Vrf
