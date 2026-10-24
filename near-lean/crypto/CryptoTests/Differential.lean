import NearCrypto
import CryptoTests.Fixtures

/-!
`crypto-differential`: the `Spec` of every primitive against its `Impl` on seeded random inputs
(a SplitMix64 stream, fixed seed, so a failure reproduces). Hashes agree on every length from 0
to 300 and on larger random lengths. Field, scalar and point operations of the fast curve
code agree with the reference ones, and `verify` agrees on valid signatures, edited signatures,
random keys and random signature bytes.
-/

open NearCrypto CryptoTests Ed25519

/-- SplitMix64. -/
structure Rng where
  state : UInt64

namespace Rng

def next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- `n` random bytes. -/
def bytes (r : Rng) (n : Nat) : ByteArray × Rng :=
  Id.run do
    let mut out := ByteArray.empty
    let mut r := r
    for _ in [0:n] do
      let (x, r') := r.next
      out := out.push x.toUInt8
      r := r'
    return (out, r)

/-- A random number below `n`. -/
def below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (x.toNat % n, r)

/-- A random number of `n` bytes. -/
def nat (r : Rng) (n : Nat) : Nat × Rng :=
  let (b, r) := r.bytes n
  (Spec.toNat b, r)

end Rng

def check (t : Tally) (name : String) (ok : Bool) (detail : String := "") : Tally :=
  t.record name (if ok then none else some detail)

def hashes : List (String × ((ByteArray → ByteArray) × (ByteArray → ByteArray))) :=
  [("sha256", (Sha256.Spec.hash, Sha256.Impl.hash)),
    ("sha512", (Sha512.Spec.hash, Sha512.Impl.hash)),
    ("keccak256", (Keccak.Spec.keccak256, Keccak.Impl.keccak256)),
    ("keccak512", (Keccak.Spec.keccak512, Keccak.Impl.keccak512)),
    ("ripemd160", (Ripemd160.Spec.hash, Ripemd160.Impl.hash)),
    ("blake2b256", (Blake2b.Spec.hash 32, Blake2b.Impl.hash 32)),
    ("blake2b512", (Blake2b.Spec.hash 64, Blake2b.Impl.hash 64))]

def hashTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for (name, spec, impl) in hashes do
      let mut lengths := List.range 301
      for _ in [0:12] do
        let (n, r') := r.below 6000
        lengths := lengths ++ [n]
        r := r'
      for n in lengths do
        let (m, r') := r.bytes n
        r := r'
        t := check t s!"{name} length {n}" (spec m == impl m) s!"digests differ on {toHex m}"
    return (t, r)

/-- HMAC-SHA256 agrees for keys shorter than, equal to and longer than a block. -/
def hmacTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for keyLen in [0, 1, 31, 32, 63, 64, 65, 100, 200] do
      let (key, r') := r.bytes keyLen
      let (msg, r') := r'.bytes (keyLen * 3 % 150)
      r := r'
      t :=
        check t s!"hmac key length {keyLen}" (Hmac.Spec.sha256 key msg == Hmac.Impl.sha256 key msg)
    return (t, r)

/-- Field elements that stress the limb boundaries. -/
def fieldEdges : List Nat :=
  [0, 1, 2, 18, 19, 20, Spec.p - 1, Spec.p, Spec.p + 1, 2 ^ 255 - 1, 2 ^ 254, 2 ^ 26, 2 ^ 26 - 1,
    2 ^ 51, 2 ^ 51 - 1, 2 ^ 230, 2 ^ 230 - 1, 2 ^ 252 + 12345, Spec.sqrtM1, Spec.d]

def fieldTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    t := check t "constant d" (Fe.d.toNat == Spec.d)
    t := check t "constant sqrt(-1)" (Fe.sqrtM1.toNat == Spec.sqrtM1)
    t := check t "constant 2d" (Fe.d2.toNat == 2 * Spec.d % Spec.p)
    t := check t "order" (ell == Spec.ell)
    t := check t "prime" (p == Spec.p)
    t := check t "base point" (Ext.compress Ext.basePoint == Spec.compress Spec.basePoint)
    let mut values := fieldEdges
    for _ in [0:60] do
      let (a, r') := r.nat 32
      r := r'
      values := values ++ [a % 2 ^ 255]
    let reduced (n : Nat) := n % Spec.p
    for a in values do
      let fa := Fe.ofNat a
      t := check t s!"toNat {a}" (fa.toNat == reduced a)
      t := check t s!"inv {a}" ((Fe.inv fa).toNat == Spec.inv a)
      t := check t s!"powP58 {a}" ((Fe.powP58 fa).toNat == Spec.powMod a ((Spec.p - 5) / 8))
      t := check t s!"sq {a}" ((Fe.sq fa).toNat == reduced (a * a))
      t := check t s!"neg {a}" ((Fe.neg fa).toNat == (Spec.p - reduced a) % Spec.p)
    for (a, b) in values.zip (values.drop 7 ++ values.take 7) do
      let (fa, fb) := (Fe.ofNat a, Fe.ofNat b)
      t := check t s!"mul {a} {b}" ((Fe.mul fa fb).toNat == reduced (a * b))
      t := check t s!"add {a} {b}" ((Fe.add fa fb).toNat == reduced (a + b))
      t :=
        check t s!"sub {a} {b}" ((Fe.sub fa fb).toNat == (reduced a + Spec.p - reduced b) % Spec.p)
      -- long chains keep every limb in range
      let chain := (List.range 20).foldl (fun x _ => Fe.sub (Fe.mul x fb) (Fe.add x fa)) fa
      let chainNat :=
        (List.range 20).foldl (fun x _ => ((x * b) % Spec.p + Spec.p - (x + a) % Spec.p) % Spec.p)
          (reduced a)
      t := check t s!"chain {a} {b}" (chain.toNat == chainNat)
      let (u, v) := (reduced a, reduced b)
      t :=
        check t s!"sqrtRatio {a} {b}"
          ((Fe.sqrtRatio fa fb).isSome == (Spec.sqrtRatio u v).isSome &&
            ((Fe.sqrtRatio fa fb).all fun x =>
              x.toNat * x.toNat % Spec.p * v % Spec.p == u ||
                x.toNat * x.toNat % Spec.p * v % Spec.p == (Spec.p - u) % Spec.p))
    return (t, r)

def scalarTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for i in [0:50] do
      let (b, r') := r.bytes 64
      r := r'
      t := check t s!"reduceWide {i}" (Scalar.reduceWide b == Spec.reduce b)
      t := check t s!"ofBytes {i}" (Scalar.ofBytes b 0 4 == Spec.toNat (b.extract 0 32))
      let n := Spec.toNat (b.extract 0 32)
      t := check t s!"toBytes32 {i}" (Scalar.toBytes32 n == Spec.ofNat 32 n)
    return (t, r)

def pointTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for i in [0:30] do
      let (a, r') := r.nat 32
      let (b, r') := r'.nat 32
      r := r'
      let a := a % 2 ^ 253
      let b := b % 2 ^ 253
      let specA := Spec.mul a Spec.basePoint
      let implA := Ext.mulBase a
      t := check t s!"mulBase {i}" (Ext.compress implA == Spec.compress specA)
      t :=
        check t s!"doubleMulBase {i}"
          (Ext.compress (Ext.doubleMulBase a implA b) ==
            Spec.compress (Spec.add (Spec.mul a specA) (Spec.mul b Spec.basePoint)))
      t :=
        check t s!"dbl {i}" (Ext.compress (Ext.dbl implA) == Spec.compress (Spec.add specA specA))
      t :=
        check t s!"add/neg {i}"
          (Ext.compress (Ext.add implA (Ext.neg implA)) == Spec.compress Spec.zero)
    -- The scalars 0, 1, ℓ - 1, ℓ (the base point has order ℓ) and 2²⁵⁵ + 1.
    for (name, k) in
      [("0", 0), ("1", 1), ("ell-1", ell - 1), ("ell", ell), ("2^255+1", 2 ^ 255 + 1)] do
      t :=
        check t s!"mulBase {name}"
          (Ext.compress (Ext.mulBase k) == Spec.compress (Spec.mul k Spec.basePoint))
    return (t, r)

/-- Random 32-byte strings decode alike, with an identical re-encoding. -/
def decodeTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for i in [0:200] do
      let (b, r') := r.bytes 32
      r := r'
      let impl := Ext.decompress b
      let spec := Spec.decompress b
      let same :=
        match impl, spec with
        | none, none => true
        | some x, some y => Ext.compress x == Spec.compress y
        | _, _ => false
      t := check t s!"decompress {i}" same s!"{toHex b}"
    return (t, r)

def signTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    for i in [0:60] do
      let (seed, r') := r.bytes 32
      let (len, r') := r'.below 200
      let (msg, r') := r'.bytes len
      let (flip, r') := r'.below 512
      let (other, r') := r'.bytes 32
      let (junk, r') := r'.bytes 64
      r := r'
      let some sk := Impl.SigningKey.ofSeed seed | t := check t s!"ofSeed {i}" false
      t := check t s!"publicKey {i}" (sk.publicKey == Spec.publicKey seed)
      let sig := sk.sign msg
      t := check t s!"sign {i}" (sig == Spec.sign seed msg)
      t :=
        check t s!"verify valid {i}"
          (Impl.verify sk.publicKey msg sig && Spec.verify sk.publicKey msg sig)
      -- one flipped bit of the signature
      let mut bad := sig
      bad := bad.set! (flip / 8) (bad.get! (flip / 8) ^^^ (1 <<< (flip % 8).toUInt8))
      t :=
        check t s!"verify edited {i}"
          (Impl.verify sk.publicKey msg bad == Spec.verify sk.publicKey msg bad)
      -- a different key and random signature bytes
      t := check t s!"verify other key {i}" (Impl.verify other msg sig == Spec.verify other msg sig)
      t :=
        check t s!"verify random signature {i}"
          (Impl.verify sk.publicKey msg junk == Spec.verify sk.publicKey msg junk)
      -- wrong lengths
      t :=
        check t s!"verify lengths {i}"
          (!Impl.verify (sk.publicKey.push 0) msg sig &&
            !Impl.verify sk.publicKey msg (sig.push 0) &&
            !Spec.verify (sk.publicKey.push 0) msg sig &&
            !Spec.verify sk.publicKey msg (sig.push 0))
    return (t, r)

/-! ### secp256k1 -/

/-- Field values that stress the limb boundaries. -/
def secpFieldEdges : List Nat :=
  [0, 1, 2, 977, 2 ^ 32, 2 ^ 32 + 977, Secp256k1.p - 1, Secp256k1.p, Secp256k1.p + 1,
    Secp256k1.p - 2 ^ 32, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 234, 2 ^ 234 - 1, 2 ^ 26, 2 ^ 26 - 1, 2 ^ 52,
    2 ^ 208 - 1, 2 ^ 128, 2 ^ 129 + 12345, Secp256k1.n, Secp256k1.n - 1]

def secpFieldTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    let p := Secp256k1.p
    t := check t "secp prime" (Secp256k1.p == Secp256k1.Spec.p)
    t := check t "secp order" (Secp256k1.n == Secp256k1.Spec.n)
    let mut values := secpFieldEdges
    for _ in [0:60] do
      let (a, r') := r.nat 32
      r := r'
      values := values ++ [a]
    for a in values do
      let fa := Secp256k1.Fp.ofNat a
      t := check t s!"secp toNat {a}" (fa.toNat == a % p)
      t := check t s!"secp isZero {a}" (fa.isZero == (a % p == 0))
      t := check t s!"secp sq {a}" ((Secp256k1.Fp.sq fa).toNat == a * a % p)
      t := check t s!"secp neg {a}" ((Secp256k1.Fp.neg fa).toNat == (p - a % p) % p)
      t := check t s!"secp inv {a}" ((Secp256k1.Fp.inv fa).toNat == Secp256k1.Spec.inv p a)
      t := check t s!"secp mulInt {a}" ((Secp256k1.Fp.mulInt fa 15632).toNat == a * 15632 % p)
      t := check t s!"secp toBytes {a}" (fa.toBytes == Secp256k1.Spec.ofNat 32 (a % p))
      let root := Secp256k1.Fp.sqrt fa
      let want := Secp256k1.Spec.sqrt a
      t :=
        check t s!"secp sqrt {a}"
          (root.isSome == want.isSome && (root.all fun x => x.toNat * x.toNat % p == a % p))
    for (a, b) in values.zip (values.drop 7 ++ values.take 7) do
      let (fa, fb) := (Secp256k1.Fp.ofNat a, Secp256k1.Fp.ofNat b)
      t := check t s!"secp mul {a} {b}" ((Secp256k1.Fp.mul fa fb).toNat == a * b % p)
      t := check t s!"secp add {a} {b}" ((Secp256k1.Fp.add fa fb).toNat == (a + b) % p)
      t := check t s!"secp sub {a} {b}" ((Secp256k1.Fp.sub fa fb).toNat == (a % p + p - b % p) % p)
      t := check t s!"secp eq {a} {b}" (Secp256k1.Fp.eq fa fb == (a % p == b % p))
      -- long chains keep every limb in range
      let chain :=
        (List.range 20).foldl
          (fun x _ => Secp256k1.Fp.sub (Secp256k1.Fp.mul x fb) (Secp256k1.Fp.add x fa)) fa
      let chainNat := (List.range 20).foldl (fun x _ => ((x * b) % p + p - (x + a) % p) % p) (a % p)
      t := check t s!"secp chain {a} {b}" (chain.toNat == chainNat)
    return (t, r)

def secpScalarTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    let n := Secp256k1.n
    for a in [1, 2, 3, n - 1, n - 2, n / 2, n / 2 + 1, 2 ^ 128, 2 ^ 255 % n] do
      t := check t s!"scalar inv {a}" (Secp256k1.Scalar.inv a n == Secp256k1.Spec.inv n a)
    for i in [0:30] do
      let (a, r') := r.nat 32
      r := r'
      let a := a % (n - 1) + 1
      t := check t s!"scalar inv random {i}" (a * Secp256k1.Scalar.inv a n % n == 1)
      let (b, r') := r.nat 32
      r := r'
      t :=
        check t s!"scalar bytes {i}"
          (Secp256k1.Scalar.ofBytes (Secp256k1.Scalar.toBytes b) == b &&
            Secp256k1.Scalar.toBytes b == Secp256k1.Spec.ofNat 32 b)
    return (t, r)

/-- An affine point of the fast code as the `Spec` one. -/
def secpSpec (P : Option Secp256k1.Aff) : Secp256k1.Spec.Point :=
  P.map fun Q => (Q.x.toNat, Q.y.toNat)

def secpPointTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    let n := Secp256k1.n
    let G := Secp256k1.Aff.base
    let specG := Secp256k1.Spec.basePoint
    t := check t "secp base point" (secpSpec (some G) == specG)
    t := check t "secp base on curve" G.onCurve
    t :=
      check t "secp base table"
        (Secp256k1.baseTable.size == 128 && secpSpec (some Secp256k1.baseTable[0]!) == specG &&
          secpSpec (some Secp256k1.baseTable[127]!) == Secp256k1.Spec.ecmult 0 none 255)
    -- scalars that exercise the recoding and the exceptional additions
    let edgeScalars :=
      [0, 1, 2, 3, 15, 16, 255, 256, 2 ^ 128, n - 1, n, n + 1, 2 ^ 255, 2 ^ 256 - 1]
    for k in edgeScalars do
      t :=
        check t s!"secp mulBase {k}"
          (secpSpec (Secp256k1.Jac.mulBase k).toAff == Secp256k1.Spec.ecmult 0 none k)
    for k in edgeScalars do
      for l in [0, 1, 2, n - 1, n, 12345, 2 ^ 200] do
        t :=
          check t s!"secp ecmult {k} {l}"
            (secpSpec (Secp256k1.Jac.ecmult k G l).toAff == Secp256k1.Spec.ecmult k specG l)
    -- a·G + b·G with a + b ≡ 0 or a = b (the doubling and the opposite cases)
    for (a, b) in [(5, n - 5), (5, 5), (n - 1, 1), (7, 7), (2 ^ 200, n - 2 ^ 200)] do
      t :=
        check t s!"secp ecmult same point {a} {b}"
          (secpSpec (Secp256k1.Jac.ecmult a G b).toAff == Secp256k1.Spec.ecmult a specG b)
    for i in [0:25] do
      let (a, r') := r.nat 32
      let (b, r') := r'.nat 32
      let (c, r') := r'.nat 32
      r := r'
      let some P := (Secp256k1.Jac.mulBase (c % n)).toAff | t := check t s!"secp point {i}" false
      let specP := secpSpec (some P)
      t :=
        check t s!"secp ecmult random {i}"
          (secpSpec (Secp256k1.Jac.ecmult a P b).toAff == Secp256k1.Spec.ecmult a specP b)
      t :=
        check t s!"secp ecmult random 2 {i}"
          (secpSpec (Secp256k1.Jac.ecmult (a % n) P (b % 2 ^ 128)).toAff ==
            Secp256k1.Spec.ecmult (a % n) specP (b % 2 ^ 128))
    return (t, r)

def secpKeyTests (t : Tally) (r : Rng) : Tally × Rng :=
  Id.run do
    let mut t := t
    let mut r := r
    let n := Secp256k1.n
    for i in [0:60] do
      let (sk, r') := r.bytes 32
      let (junk, r') := r'.bytes 65
      let (msg, r') := r'.bytes 32
      let (flip, r') := r'.below 520
      let (small, r') := r'.below 130
      r := r'
      -- the secret key is valid for most `i`; the others cover 0, n and 2^256 - 1
      let sk :=
        match i % 20 with
        | 7 => zeros 32
        | 11 => Secp256k1.Spec.ofNat 32 n
        | 13 => ByteArray.mk (Array.replicate 32 0xff)
        | _ => sk
      t :=
        check t s!"secp validSecret {i}"
          (Secp256k1.Impl.validSecret sk == Secp256k1.Spec.validSecret sk)
      t :=
        check t s!"secp publicKey {i}"
          (Secp256k1.Impl.publicKey sk ==
            (Secp256k1.Spec.publicKey sk).map fun (x, y) => Secp256k1.Spec.serializeRaw x y)
      let sig := Secp256k1.Impl.signRecoverable sk msg
      t := check t s!"secp sign {i}" (sig == Secp256k1.Spec.signRecoverable sk msg)
      if let some sig := sig then
        let some pk := Secp256k1.Impl.publicKey sk | t := check t s!"secp key {i}" false
        t :=
          check t s!"secp verify {i}"
            (Secp256k1.Impl.verify pk msg sig && Secp256k1.Spec.verify pk msg sig)
        t :=
          check t s!"secp recover {i}"
            (Secp256k1.Impl.recoverKey msg sig == some pk &&
              Secp256k1.Spec.recoverKey msg sig == some pk)
        -- one flipped bit of the signature or of the key
        let flipBit (b : ByteArray) (k : Nat) : ByteArray :=
          b.set! (k / 8) (b.get! (k / 8) ^^^ (1 <<< (k % 8).toUInt8))
        let bad := flipBit sig (flip % 520)
        t :=
          check t s!"secp verify edited {i}"
            (Secp256k1.Impl.verify pk msg bad == Secp256k1.Spec.verify pk msg bad)
        t :=
          check t s!"secp recover edited {i}"
            (Secp256k1.Impl.recoverKey msg bad == Secp256k1.Spec.recoverKey msg bad)
        let badKey := flipBit pk (flip % 512)
        t :=
          check t s!"secp verify edited key {i}"
            (Secp256k1.Impl.verify badKey msg sig == Secp256k1.Spec.verify badKey msg sig)
        -- the high-s twin: recovers the same key with the other parity, never verifies
        let s := Secp256k1.Scalar.ofBytes sig 32
        let high :=
          sig.extract 0 32 ++ Secp256k1.Scalar.toBytes (n - s) ++
            (ByteArray.empty.push (sig.get! 64 ^^^ 1))
        t :=
          check t s!"secp high-s {i}"
            (!Secp256k1.Impl.verify pk msg high && !Secp256k1.Spec.verify pk msg high &&
              Secp256k1.Impl.recoverKey msg high == some pk)
      -- random signatures: small `r` gives the recovery ids 2 and 3
      let rSmall := Secp256k1.Spec.toNat (junk.extract 0 (small / 8 + 1)) % 2 ^ (small + 1)
      for v in ([0, 1, 2, 3] : List Nat) do
        let rs := Secp256k1.Spec.ofNat 32 rSmall ++ junk.extract 32 64
        let s65 := rs.push v.toUInt8
        let implKey := Secp256k1.Impl.recoverKey msg s65
        t := check t s!"secp recover small r {i} {v}" (implKey == Secp256k1.Spec.recoverKey msg s65)
        t :=
          check t s!"secp ecrecover {i} {v}"
            (Secp256k1.Impl.ecrecover msg rs v false == Secp256k1.Spec.ecrecover msg rs v false &&
              Secp256k1.Impl.ecrecover msg rs v true == Secp256k1.Spec.ecrecover msg rs v true)
        let rs2 := junk.extract 0 64
        t :=
          check t s!"secp recover random {i} {v}"
            (Secp256k1.Impl.recoverKey msg (rs2.push v.toUInt8) ==
              Secp256k1.Spec.recoverKey msg (rs2.push v.toUInt8))
      -- public key parsing of random 33 and 65 byte strings, with the tags that parse
      let tag : UInt8 := [2, 3, 4, 6, 7, 0, 5][i % 7]!
      let candidate :=
        (ByteArray.empty.push tag) ++ junk.extract 0 (if tag == 2 || tag == 3 then 32 else 64)
      t :=
        check t s!"secp parse random {i}"
          ((Secp256k1.Impl.parsePublicKey candidate).map Secp256k1.Impl.serializeRaw ==
            (Secp256k1.Spec.parsePublicKey candidate).map fun (x, y) =>
              Secp256k1.Spec.serializeRaw x y)
    return (t, r)

def main : IO UInt32 := do
  let mut t : Tally := {}
  let mut r : Rng := ⟨0x4e45415243525950⟩
  (t, r) := hashTests t r
  (t, r) := hmacTests t r
  (t, r) := fieldTests t r
  (t, r) := scalarTests t r
  (t, r) := pointTests t r
  (t, r) := decodeTests t r
  (t, r) := signTests t r
  (t, r) := secpFieldTests t r
  (t, r) := secpScalarTests t r
  (t, r) := secpPointTests t r
  (t, r) := secpKeyTests t r
  finish "crypto-differential" t
