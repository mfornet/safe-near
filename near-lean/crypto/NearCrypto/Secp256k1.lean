import NearCrypto.Secp256k1.Curve
import NearCrypto.Secp256k1.Spec
import NearCrypto.Hmac

/-!
# secp256k1 ECDSA

`Impl` accepts and returns exactly what `libsecp256k1` (through `secp256k1` 0.27.0 and
`near-crypto` 0.37.4) does; see `Secp256k1.Spec` for the rules and their sources. Public keys are
the 64 bytes `x ‖ y` that `near-crypto` stores, signatures the 65 bytes `r ‖ s ‖ v` of
`Secp256K1Signature`, secret keys 32 big-endian bytes.
-/

namespace NearCrypto.Secp256k1

/-! ### Scalars -/

namespace Scalar

/-- The big-endian value of the 32 bytes at offset `off`. -/
def ofBytes (b : ByteArray) (off : Nat := 0) : Nat :=
  (be64 b off).toNat <<< 192 ||| (be64 b (off + 8)).toNat <<< 128 |||
    (be64 b (off + 16)).toNat <<< 64 |||
    (be64 b (off + 24)).toNat

/-- The 32 big-endian bytes of `x < 2²⁵⁶`. -/
def toBytes (x : Nat) : ByteArray :=
  pushBe64
    (pushBe64 (pushBe64 (pushBe64 ByteArray.empty (x >>> 192).toUInt64) (x >>> 128).toUInt64)
      (x >>> 64).toUInt64)
    x.toUInt64

/-- The inverse of `a ≠ 0` modulo the prime `m`, by the extended Euclidean algorithm. -/
def inv (a m : Nat) : Nat :=
  let rec go : Nat → Nat → Nat → Int → Int → Nat
    | 0, _, _, _, _ => 0
    | fuel + 1, r0, r1, t0, t1 =>
      if r1 == 0 then (t0 % (m : Int)).toNat
      else
        let q := r0 / r1
        go fuel r1 (r0 - q * r1) t1 (t0 - (q : Int) * t1)
  go 600 m a 0 1

end Scalar

namespace Impl

open Fp

/-- `secp256k1_eckey_pubkey_parse`. -/
def parsePublicKey (b : ByteArray) : Option Aff :=
  if b.size == 33 && (b.get! 0 == 2 || b.get! 0 == 3) then
    let x := Scalar.ofBytes b 1
    if x < p then
      let fx := Fp.ofNat x
      match Fp.sqrt (curveRhs fx) with
      | none => none
      | some y =>
        let y := if (y.toNat % 2 == 1) == (b.get! 0 == 3) then y else Fp.neg y
        some ⟨fx, y⟩
    else none
  else
    if b.size == 65 && (b.get! 0 == 4 || b.get! 0 == 6 || b.get! 0 == 7) then
      let x := Scalar.ofBytes b 1
      let y := Scalar.ofBytes b 33
      if x < p && y < p && (b.get! 0 == 4 || (y % 2 == 1) == (b.get! 0 == 7)) then
        let P : Aff := ⟨Fp.ofNat x, Fp.ofNat y⟩
        if P.onCurve then some P else none
      else none
    else none

/-- The 64 bytes `x ‖ y`. -/
def serializeRaw (P : Aff) : ByteArray :=
  Scalar.toBytes P.x.toNat ++ Scalar.toBytes P.y.toNat

/-- The 65-byte form with tag `04`. -/
def serializeUncompressed (P : Aff) : ByteArray :=
  (ByteArray.empty.push 4) ++ serializeRaw P

/-- The 33-byte form. -/
def serializeCompressed (P : Aff) : ByteArray :=
  (ByteArray.empty.push (if P.y.toNat % 2 == 1 then 3 else 2)) ++ Scalar.toBytes P.x.toNat

/-- Whether `x` is the abscissa of `R` modulo `n`: `x = r` or (`r + n < p` and `x = r + n`), compared
without inverting `Z` (`secp256k1_gej_eq_x_var`). -/
def abscissaIs (R : Jac) (r : Nat) : Bool :=
  let z2 := sq R.z
  Fp.eq (mul (Fp.ofNat r) z2) R.x || (r < p - n && Fp.eq (mul (Fp.ofNat (r + n)) z2) R.x)

/-- `secp256k1_ecdsa_verify` for the scalars `r`, `s`, the reduced message `m` and the key. -/
def verifyScalars (r s m : Nat) (pk : Aff) : Bool :=
  if r == 0 || s == 0 || s ≥ n / 2 + 1 then false
  else
    let sn := Scalar.inv s n
    let R := Jac.ecmult (sn * r % n) pk (sn * m % n)
    !R.inf && abscissaIs R r

/-- `near_crypto::Signature::verify` for SECP256K1: the 64-byte key, the message, the 65-byte
signature `r ‖ s ‖ v`. -/
def verify (pk msg sig : ByteArray) : Bool :=
  if pk.size != 64 || sig.size != 65 || msg.size != 32 || sig.get! 64 ≥ 4 then false
  else
    let r := Scalar.ofBytes sig 0
    let s := Scalar.ofBytes sig 32
    if r ≥ n || s ≥ n then false
    else
      match parsePublicKey ((ByteArray.empty.push 4) ++ pk) with
      | none => false
      | some q => verifyScalars r s (Scalar.ofBytes msg % n) q

/-- `secp256k1_ecdsa_sig_recover`: `m` is the message already reduced modulo `n`. -/
def recover (r s recid m : Nat) : Option Aff :=
  if r == 0 || s == 0 then none
  else
    if recid ≥ 2 && r ≥ p - n then none
    else
      let fx := Fp.ofNat (if recid ≥ 2 then r + n else r)
      match Fp.sqrt (curveRhs fx) with
      | none => none
      | some y =>
        let y := if y.toNat % 2 == recid % 2 then y else Fp.neg y
        let rn := Scalar.inv r n
        (Jac.ecmult (rn * s % n) ⟨fx, y⟩ ((n - rn * m % n) % n)).toAff

/-- The 64-byte public key of a signature `r ‖ s ‖ v` over a 32-byte message
(`Secp256K1Signature::recover` after `RecoverableSignature::from_compact`). -/
def recoverKey (msg sig : ByteArray) : Option ByteArray :=
  if msg.size != 32 || sig.size != 65 || sig.get! 64 ≥ 4 then none
  else
    let r := Scalar.ofBytes sig 0
    let s := Scalar.ofBytes sig 32
    if r ≥ n || s ≥ n then none
    else (recover r s (sig.get! 64).toNat (Scalar.ofBytes msg % n)).map serializeRaw

/-- The VM host function `ecrecover(hash, sig, v, malleability)` once the VM has checked the
argument lengths, `v < 4` and the flag: the 64-byte key, or `none` for a signature that is not
valid. -/
def ecrecover (hash sig : ByteArray) (v : Nat) (malleability : Bool) : Option ByteArray :=
  if hash.size != 32 || sig.size != 64 || v ≥ 4 then none
  else
    let r := Scalar.ofBytes sig 0
    let s := Scalar.ofBytes sig 32
    if r ≥ n || s ≥ (if malleability then n / 2 + 1 else n) then none
    else (recover r s v (Scalar.ofBytes hash % n)).map serializeRaw

/-! ### Keys and signing -/

/-- A secret key: 32 bytes, not zero and below `n` (`secp256k1_ec_seckey_verify`). -/
def validSecret (b : ByteArray) : Bool :=
  b.size == 32 && 0 < Scalar.ofBytes b && Scalar.ofBytes b < n

/-- The 64-byte public key of a valid secret key. -/
def publicKey (sk : ByteArray) : Option ByteArray :=
  if validSecret sk then (Jac.mulBase (Scalar.ofBytes sk)).toAff.map serializeRaw else none

/-- The state of `secp256k1_rfc6979_hmac_sha256`. -/
structure Drbg where
  k : ByteArray
  v : ByteArray
  retry : Bool

/-- Seed with `key = seckey ‖ reduced message`. -/
def Drbg.init (key : ByteArray) : Drbg :=
  let v := ByteArray.mk (Array.replicate 32 1)
  let k := zeros 32
  let k := Hmac.Impl.sha256 k (v ++ (ByteArray.empty.push 0) ++ key)
  let v := Hmac.Impl.sha256 k v
  let k := Hmac.Impl.sha256 k (v ++ (ByteArray.empty.push 1) ++ key)
  { k, v := Hmac.Impl.sha256 k v, retry := false }

/-- The next 32 bytes. -/
def Drbg.generate (d : Drbg) : ByteArray × Drbg :=
  let (k, v) :=
    if d.retry then
      let k := Hmac.Impl.sha256 d.k (d.v ++ (ByteArray.empty.push 0))
      (k, Hmac.Impl.sha256 k d.v)
    else (d.k, d.v)
  let v := Hmac.Impl.sha256 k v
  (v, { k, v, retry := true })

/-- `secp256k1_nonce_function_rfc6979`: the nonce of attempt `counter`. -/
def nonce (key32 : ByteArray) (m : Nat) (counter : Nat) : Nat :=
  let rec go : Nat → Drbg → ByteArray → ByteArray
    | 0, _, out => out
    | k + 1, d, _ =>
      let (out, d) := d.generate
      go k d out
  Scalar.ofBytes (go (counter + 1) (Drbg.init (key32 ++ Scalar.toBytes m)) ByteArray.empty)

/-- `secp256k1_ecdsa_sign_recoverable`: the 65 bytes `r ‖ s ‖ v` of a valid secret key and a
32-byte message, or `none`. Not constant time. -/
def signRecoverable (sk msg : ByteArray) : Option ByteArray :=
  if !validSecret sk || msg.size != 32 then none
  else
    let d := Scalar.ofBytes sk
    let m := Scalar.ofBytes msg % n
    let attempt (count : Nat) : Option ByteArray :=
      let k := nonce sk m count
      if k == 0 || k ≥ n then none
      else
        match (Jac.mulBase k).toAff with
        | none => none
        | some R =>
          let rx := R.x.toNat
          let r := rx % n
          let s := Scalar.inv k n * ((m + r * d) % n) % n
          let high := s ≥ n / 2 + 1
          let s := if high then n - s else s
          let recid := (if rx ≥ n then 2 else 0) + (if (R.y.toNat % 2 == 1) != high then 1 else 0)
          if r == 0 || s == 0 then none
          else some (Scalar.toBytes r ++ Scalar.toBytes s ++ (ByteArray.empty.push recid.toUInt8))
    (List.range 64).findSome? attempt

end Impl

end NearCrypto.Secp256k1

namespace NearCrypto

/-- `near_crypto::Signature::verify` for SECP256K1: public key (64 bytes), message (32 bytes),
signature (65 bytes). -/
def secp256k1Verify (pk msg sig : ByteArray) : Bool :=
  Secp256k1.Impl.verify pk msg sig

/-- The VM's `ecrecover(hash, sig, v, malleability_flag)` for arguments the VM has checked (32 and
64 bytes, `v < 4`, flag 0 or 1): the 64-byte key, or `none` when the host function returns 0. -/
def ecrecover (hash sig : ByteArray) (v : Nat) (malleability : Bool) : Option ByteArray :=
  Secp256k1.Impl.ecrecover hash sig v malleability

end NearCrypto
