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
    ("ripemd160", (Ripemd160.Spec.hash, Ripemd160.Impl.hash))]

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

def main : IO UInt32 := do
  let mut t : Tally := {}
  let mut r : Rng := ⟨0x4e45415243525950⟩
  (t, r) := hashTests t r
  (t, r) := fieldTests t r
  (t, r) := scalarTests t r
  (t, r) := pointTests t r
  (t, r) := decodeTests t r
  (t, r) := signTests t r
  finish "crypto-differential" t
