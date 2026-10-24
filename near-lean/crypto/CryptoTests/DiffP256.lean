import NearCrypto
import CryptoTests.Fixtures
import CryptoTests.Rng

/-!
Differential tests of `NearCrypto.P256`: the fast verification against the reference one on
signatures made here (any message length), edited signatures, random keys and bytes, and a
signature made for a digest that agrees with the signed one in its first 32 bytes only.
-/

namespace CryptoTests.DiffP256

open NearCrypto NearCrypto.P256 NearCrypto.Pairing

def chk (t : Tally) (name : String) (ok : Bool) (detail : String := "") : Tally :=
  t.record name (if ok then none else some detail)

def below (r : Rng) (m : Nat) : Nat × Rng :=
  let (b, r) := r.bytes (m.log2 / 8 + 9)
  (beNat b 0 b.size % m, r)

/-- The compressed key of the secret `d`. -/
def keyOf (d : Nat) : ByteArray :=
  match Impl.mulAdd d (gx, gy) 0 with
  | some (x, y) => (ByteArray.mk #[if y % 2 == 1 then 3 else 2]) ++ toBe x 32
  | none => ByteArray.empty

/-- `r ‖ s` of ECDSA with the nonce `k` over the digest bytes `msg`; `none` if `r` or `s` is zero. -/
def sign (d k : Nat) (msg : ByteArray) : Option ByteArray :=
  match Impl.mulAdd k (gx, gy) 0 with
  | none => none
  | some (x, _) =>
    let rr := x % n
    let z := beNat msg 0 (min 32 msg.size) % n
    let s := invMod n k * ((z + rr * d) % n) % n
    if rr == 0 || s == 0 then none else some (toBe rr 32 ++ toBe s 32)

def tests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for i in [0:24] do
      let (d, r1) := below r (n - 1)
      let (k, r2) := below r1 (n - 1)
      let (len, r3) := below r2 80
      let (m, r4) := r3.bytes len
      r := r4
      let d := d + 1
      let k := k + 1
      let pk := keyOf d
      match sign d k m with
      | none =>
        pure ()
      | some sig =>
        let good := Spec.verify sig m pk
        let fast := Impl.verify sig m pk
        t :=
          chk t s!"p256 sign verifies {i} (length {len})"
            (good.toOption == some (decide (len ≥ 16)) && fast.toOption == some (decide (len ≥ 16)))
        -- edited signature, message and key
        let (pos, r5) := below r 64
        let (bit, r6) := below r5 8
        r := r6
        let sig' := sig.set! pos (sig.get! pos ^^^ (1 <<< bit.toUInt8))
        t :=
          chk t s!"p256 edited signature {i}"
            ((Spec.verify sig' m pk).toOption == (Impl.verify sig' m pk).toOption)
        let m' := if m.size == 0 then m else m.set! (pos % m.size) (m.get! (pos % m.size) ^^^ 1)
        t :=
          chk t s!"p256 edited message {i}"
            ((Spec.verify sig m' pk).toOption == (Impl.verify sig m' pk).toOption)
        let pk' := pk.set! (1 + pos % 32) (pk.get! (1 + pos % 32) ^^^ 1)
        t :=
          chk t s!"p256 edited key {i}"
            ((Spec.verify sig m pk').toOption == (Impl.verify sig m pk').toOption)
        -- the bytes beyond the first 32 are not read
        if len > 32 then
          t :=
            chk t s!"p256 tail ignored {i}"
              ((Impl.verify sig (m.extract 0 32 ++ ByteArray.mk #[1, 2, 3]) pk).toOption ==
                good.toOption)
    -- random keys and signatures
    for i in [0:24] do
      let (sig, r1) := r.bytes 64
      let (key, r2) := r1.bytes 33
      let (m, r3) := r2.bytes 40
      r := r3
      let key := key.set! 0 (if i % 2 == 0 then 2 else 3)
      t :=
        chk t s!"p256 random {i}"
          ((Spec.verify sig m key).toOption == (Impl.verify sig m key).toOption)
    return (t, r)

end CryptoTests.DiffP256
