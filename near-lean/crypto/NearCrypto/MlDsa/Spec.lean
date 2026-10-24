import NearCrypto.Shake
import NearCrypto.SpecConstants

/-!
# ML-DSA-65, the specification

FIPS 204 (final) for the parameter set ML-DSA-65, written as the standard writes it: polynomials
are arrays of 256 `Int`, vectors arrays of polynomials, the NTT is algorithms 41 and 42 with the
zetas computed as powers of 1753, the encodings go through bit lists and every sampler reads a
SHAKE stream long enough (doubling the length until it is). It is slow and meant to be read.

What `near-crypto` 0.37.4 uses (`aws-lc-rs` 1.16.2, AWS-LC's `mldsa-native`) is matched on these points:

* **Pure mode, empty context.** `sign` and `verify` take `M' = 0x00 ‖ 0x00 ‖ M` (`ML-DSA.Sign` with
  a context string of length 0); nothing else is accepted, in particular not HashML-DSA, a
  non-empty context or an external `μ` for a different `M'`.
* **Keys.** The 32-byte seed `ξ` of `ML-DSA.KeyGen_internal`; a public key is 1952 bytes, a secret key
  4032 (`ρ ‖ K ‖ tr ‖ s1 ‖ s2 ‖ t0`, FIPS 204 `skEncode`) and a signature 3309.
  A secret key is accepted (`ml_dsa_65_pack_pk_from_sk`) only if `s1` and `s2` lie in `[-η, η]` and
  `t0` and `tr` are the ones recomputed from `ρ`, `s1`, `s2`; `K` is free.
* **Verification** rejects a signature of another length, a malformed hint (a count that decreases
  or exceeds `ω`, indices that are not strictly increasing within a polynomial, a nonzero byte
  after the last index), `‖z‖∞ ≥ γ1 - β`, and any `c~` that is not `H(μ ‖ w1Encode(UseHint(h, Az - ct1·2^d)))`.
  Public keys are not validated beyond their length (every 10-bit `t1` is valid).
* **Signing** is the rejection loop of algorithm 7 with `ρ'' = H(K ‖ rnd ‖ μ)` (hedged: `rnd` is 32
  random bytes in `near-crypto`; the all-zero `rnd` is the deterministic variant) and at most
  13106 attempts, after which `mldsa-native` fails.
-/

namespace NearCrypto.MlDsa.Spec

open NearCrypto

/-- A polynomial: 256 coefficients. -/
abbrev Poly :=
  Array Int

/-- A vector of polynomials. -/
abbrev Vec :=
  Array Poly

/-- The modulus. -/
def q : Int :=
  8380417

/-- Dropped bits of `t`. -/
def dropped : Nat :=
  13

/-- Weight of the challenge. -/
def tau : Nat :=
  49

/-- The rows and columns of `A`. -/
def dimK : Nat :=
  6

def dimL : Nat :=
  5

/-- Range of the coefficients of `y`. -/
def gamma1 : Int :=
  2 ^ 19

/-- Low-order rounding range. -/
def gamma2 : Int :=
  (q - 1) / 32

/-- Bound of the coefficients of `s1` and `s2`. -/
def eta : Int :=
  4

/-- `τ η`. -/
def beta : Int :=
  196

/-- Maximum number of ones in the hint. -/
def omega : Nat :=
  55

/-- The length of `c~`: `λ / 4` bytes. -/
def ctildeBytes : Nat :=
  48

def pkBytes : Nat :=
  1952

def skBytes : Nat :=
  4032

def sigBytes : Nat :=
  3309

/-! ### Arithmetic -/

/-- `r mod± m`. -/
def modPm (r m : Int) : Int :=
  let r' := r % m
  if r' > m / 2 then r' - m else r'

/-- The infinity norm of a polynomial, its coefficients taken in `(-q/2, q/2]`. -/
def norm (p : Poly) : Int :=
  p.foldl (fun m x => max m (modPm x q).natAbs) 0

/-- `ν ^ (brv8 i)`'s exponent: the 8-bit reversal. -/
def brv8 (n : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc ||| (((n >>> i) &&& 1) <<< (7 - i))) 0

/-- `b ^ e mod m`. -/
def powMod (b e m : Nat) : Nat :=
  (List.range e).foldl (fun a _ => a * b % m) 1

/-- `ζ ^ brv8(i) mod q` with `ζ = 1753`. -/
def zetas : Array Int :=
  (Array.range 256).map fun i => ((powMod 1753 (brv8 i) 8380417 : Nat) : Int)

/-- Algorithm 41. -/
def ntt (f : Poly) : Poly :=
  Id.run do
    let mut w := f
    let mut m := 0
    for len in [128, 64, 32, 16, 8, 4, 2, 1] do
      for blk in [0:128 / len] do
        m := m + 1
        let z := zetas[m]!
        let start := blk * 2 * len
        for j in [start:start + len] do
          let t := z * w[j + len]! % q
          w := w.set! (j + len) ((w[j]! - t) % q)
          w := w.set! j ((w[j]! + t) % q)
    return w

/-- Algorithm 42. -/
def invNtt (f : Poly) : Poly :=
  Id.run do
    let mut w := f
    let mut m := 256
    for len in [1, 2, 4, 8, 16, 32, 64, 128] do
      for blk in [0:128 / len] do
        m := m - 1
        let z := (-zetas[m]!) % q
        let start := blk * 2 * len
        for j in [start:start + len] do
          let t := w[j]!
          let u := w[j + len]!
          w := w.set! j ((t + u) % q)
          w := w.set! (j + len) (z * (t - u) % q)
    return w.map fun x => x * 8347681 % q

/-- Coefficientwise `f` of two polynomials. -/
def zipPoly (f : Int → Int → Int) (a b : Poly) : Poly :=
  (Array.range 256).map fun i => f a[i]! b[i]!

def padd (a b : Poly) : Poly :=
  zipPoly (fun x y => (x + y) % q) a b

def psub (a b : Poly) : Poly :=
  zipPoly (fun x y => (x - y) % q) a b

/-- Product in the NTT domain. -/
def pmul (a b : Poly) : Poly :=
  zipPoly (fun x y => x * y % q) a b

def zeroPoly : Poly :=
  Array.replicate 256 0

def vzip (f : Poly → Poly → Poly) (a b : Vec) : Vec :=
  (Array.range a.size).map fun i => f a[i]! b[i]!

/-- `Â ∘ v` in the NTT domain. -/
def matVec (a : Array Vec) (v : Vec) : Vec :=
  a.map fun row => (List.range row.size).foldl (fun acc j => padd acc (pmul row[j]! v[j]!)) zeroPoly

/-! ### Rounding -/

/-- Algorithm 35. -/
def power2Round (r : Int) : Int × Int :=
  let rp := r % q
  let r0 := modPm rp (2 ^ dropped)
  ((rp - r0) / 2 ^ dropped, r0)

/-- Algorithm 36. -/
def decompose (r : Int) : Int × Int :=
  let rp := r % q
  let r0 := modPm rp (2 * gamma2)
  if rp - r0 == q - 1 then (0, r0 - 1) else ((rp - r0) / (2 * gamma2), r0)

def highBits (r : Int) : Int :=
  (decompose r).1

def lowBits (r : Int) : Int :=
  (decompose r).2

/-- Algorithm 39. -/
def makeHint (z r : Int) : Bool :=
  highBits r != highBits (r + z)

/-- Algorithm 40. -/
def useHint (h : Bool) (r : Int) : Int :=
  let m := (q - 1) / (2 * gamma2)
  let (r1, r0) := decompose r
  if h && r0 > 0 then (r1 + 1) % m else if h then (r1 - 1) % m else r1

/-! ### Bit packing -/

/-- The `n` low bits of `x`, least significant first. -/
def bitsOf (x : Nat) (n : Nat) : List Bool :=
  (List.range n).map fun i => x.testBit i

/-- Algorithm 12: bit `i` is bit `i % 8` of byte `i / 8`. -/
def bitsToBytes (bs : List Bool) : List UInt8 :=
  (SpecConstants.chunks 8 bs).map fun c =>
    c.zipIdx.foldl (fun acc (b, i) => if b then acc ||| ((1 : UInt8) <<< i.toUInt8) else acc) 0

def bytesToBits (bs : List UInt8) : List Bool :=
  bs.flatMap fun b => (List.range 8).map fun i => b.toNat.testBit i

/-- Pack naturals of `bits` bits each. -/
def packNats (vals : List Nat) (bits : Nat) : List UInt8 :=
  bitsToBytes (vals.flatMap fun v => bitsOf v bits)

/-- Unpack `count` naturals of `bits` bits each. -/
def unpackNats (bs : List UInt8) (bits count : Nat) : List Nat :=
  ((SpecConstants.chunks bits (bytesToBits bs)).take count).map fun c =>
    c.zipIdx.foldl (fun acc (b, i) => if b then acc + 2 ^ i else acc) 0

/-- Algorithm 17, `BitPack(w, a, b)` with `bits = bitlen(a + b)`: the coefficients `b - w_i`. -/
def bitPack (w : Poly) (b : Int) (bits : Nat) : List UInt8 :=
  packNats (w.toList.map fun x => (b - x).toNat) bits

/-- Algorithm 19, `BitUnpack`. -/
def bitUnpack (v : List UInt8) (b : Int) (bits : Nat) : Poly :=
  ((unpackNats v bits 256).map fun (x : Nat) => b - (x : Int)).toArray

/-- Algorithm 16, `SimpleBitPack`. -/
def simplePack (w : Poly) (bits : Nat) : List UInt8 :=
  packNats (w.toList.map Int.toNat) bits

def simpleUnpack (v : List UInt8) (bits : Nat) : Poly :=
  ((unpackNats v bits 256).map fun (x : Nat) => (x : Int)).toArray

/-- `n` chunks of `size` bytes of `bs`, each unpacked by `f`. -/
def unpackVec (bs : List UInt8) (size n : Nat) (f : List UInt8 → Poly) : Vec :=
  ((SpecConstants.chunks size bs).take n).map f |>.toArray

/-- Algorithm 20 (`HintBitPack`). -/
def hintBitPack (h : Vec) : List UInt8 :=
  let idx := h.toList.map fun p => (List.range 256).filter fun j => p[j]! != 0
  let total := (idx.map List.length).sum
  let counts := (List.range dimK).map fun i => ((idx.take (i + 1)).map List.length).sum
  idx.flatten.map (·.toUInt8) ++ List.replicate (omega - total) 0 ++ counts.map (·.toUInt8)

/-- Algorithm 21 (`HintBitUnpack`): `none` for a malformed hint. -/
def hintBitUnpack (y : Array UInt8) : Option Vec :=
  Id.run do
    let mut h : Vec := Array.replicate dimK zeroPoly
    let mut index := 0
    for i in [0:dimK] do
      let cnt := y[omega + i]!.toNat
      if cnt < index || cnt > omega then
        return none
      let first := index
      while index < cnt do
        if index > first && y[index - 1]! ≥ y[index]! then
          return none
        h := h.set! i (h[i]!.set! y[index]!.toNat 1)
        index := index + 1
    for j in [index:omega] do
      if y[j]! != 0 then
        return none
    return some h

/-! ### Encodings -/

def pkEncode (rho : ByteArray) (t1 : Vec) : ByteArray :=
  rho ++ ⟨(t1.toList.flatMap fun p => simplePack p 10).toArray⟩

def pkDecode (pk : ByteArray) : ByteArray × Vec :=
  (pk.extract 0 32, unpackVec (pk.extract 32 pk.size).toList 320 dimK (simpleUnpack · 10))

def skEncode (rho key tr : ByteArray) (s1 s2 t0 : Vec) : ByteArray :=
  let pack (v : Vec) (b : Int) (bits : Nat) : ByteArray :=
    ⟨(v.toList.flatMap fun p => bitPack p b bits).toArray⟩
  rho ++ key ++ tr ++ pack s1 eta 4 ++ pack s2 eta 4 ++ pack t0 (2 ^ 12) 13

/-- The parts of a secret key as `skDecode` reads them (nothing is checked). -/
structure Sk where
  rho : ByteArray
  key : ByteArray
  tr : ByteArray
  s1 : Vec
  s2 : Vec
  t0 : Vec

def skDecode (sk : ByteArray) : Sk :=
  let part (off n : Nat) := (sk.extract off (off + n)).toList
  { rho := sk.extract 0 32, key := sk.extract 32 64, tr := sk.extract 64 128,
    s1 := unpackVec (part 128 (dimL * 128)) 128 dimL (bitUnpack · eta 4),
    s2 := unpackVec (part (128 + dimL * 128) (dimK * 128)) 128 dimK (bitUnpack · eta 4),
    t0 :=
      unpackVec (part (128 + (dimL + dimK) * 128) (dimK * 416)) 416 dimK (bitUnpack · (2 ^ 12) 13) }

def w1Encode (w1 : Vec) : ByteArray :=
  ⟨(w1.toList.flatMap fun p => simplePack p 4).toArray⟩

def sigEncode (ctilde : ByteArray) (z h : Vec) : ByteArray :=
  ctilde ++ ⟨(z.toList.flatMap fun p => bitPack p gamma1 20).toArray⟩ ++ ⟨(hintBitPack h).toArray⟩

/-- Algorithm 27: `none` for a malformed hint. -/
def sigDecode (sig : ByteArray) : Option (ByteArray × Vec × Vec) := do
  let z :=
    unpackVec (sig.extract ctildeBytes (ctildeBytes + dimL * 640)).toList 640 dimL
      (bitUnpack · gamma1 20)
  let h ← hintBitUnpack (sig.extract (ctildeBytes + dimL * 640) sig.size).data
  pure (sig.extract 0 ctildeBytes, z, h)

/-! ### Sampling -/

def H (m : ByteArray) (n : Nat) : ByteArray :=
  Shake.Spec.shake256 m n

/-- The first 256 coefficients `extract` finds in `stream n` (`n` bytes of a SHAKE stream), doubling
`n` until there are enough. -/
def sampled (stream : Nat → ByteArray) (extract : List UInt8 → List Int) (n : Nat) : Nat → Poly
  | 0 => zeroPoly
  | fuel + 1 =>
    let cs := extract (stream n).toList
    if 256 ≤ cs.length then (cs.take 256).toArray else sampled stream extract (2 * n) fuel

/-- Algorithm 14, `CoeffFromThreeBytes`, over a stream. -/
def rejNtt : List UInt8 → List Int
  | a :: b :: c :: rest =>
    let z : Int := a.toNat + 256 * b.toNat + 65536 * (c.toNat % 128)
    (if z < q then [z] else []) ++ rejNtt rest
  | _ => []

/-- Algorithm 15, `CoeffFromHalfByte` for `η = 4`, over a stream: the low nibble first. -/
def rejBounded : List UInt8 → List Int
  | [] => []
  | z :: rest =>
    let coef (b : Nat) : List Int := if b < 9 then [4 - (b : Int)] else []
    coef (z.toNat % 16) ++ coef (z.toNat / 16) ++ rejBounded rest

def le16 (x : Nat) : ByteArray :=
  ⟨#[x.toUInt8, (x / 256).toUInt8]⟩

/-- Algorithm 32. -/
def expandA (rho : ByteArray) : Array Vec :=
  (Array.range dimK).map fun r =>
    (Array.range dimL).map fun s =>
      sampled (Shake.Spec.shake128 (rho ++ ⟨#[s.toUInt8, r.toUInt8]⟩)) rejNtt 840 10

/-- Algorithm 33. -/
def expandS (rho : ByteArray) : Vec × Vec :=
  let poly (r : Nat) : Poly := sampled (Shake.Spec.shake256 (rho ++ le16 r)) rejBounded 272 10
  ((Array.range dimL).map poly, (Array.range dimK).map fun r => poly (r + dimL))

/-- Algorithm 34. -/
def expandMask (rho : ByteArray) (mu : Nat) : Vec :=
  (Array.range dimL).map fun r => bitUnpack (H (rho ++ le16 (mu + r)) 640).toList gamma1 20

/-- Algorithm 29: `none` when the stream is too short (then the caller reads more). -/
def ballFrom (signs : Nat) (js : List UInt8) : Option Poly :=
  let skip (i : Nat) : List UInt8 → Option (Nat × List UInt8) := fun l =>
    match l.dropWhile fun j => j.toNat > i with
    | [] => none
    | j :: rest => some (j.toNat, rest)
  ((List.range tau).foldl
        (fun (acc : Option (Poly × List UInt8)) t =>
          acc.bind fun (c, l) =>
            let i := 256 - tau + t
            (skip i l).map fun (j, rest) =>
              let c := c.set! i c[j]!
              (c.set! j (if signs.testBit t then -1 else 1), rest))
        (some (zeroPoly, js))).map
    (·.1)

/-- `SampleInBall` over the first `n` bytes of the stream, doubling `n` while it runs out. -/
def sampleInBallFrom (rho : ByteArray) (n : Nat) : Nat → Poly
  | 0 => zeroPoly
  | fuel + 1 =>
    let s := (H rho n).toList
    let signs := (s.take 8).zipIdx.foldl (fun acc (b, i) => acc + b.toNat * 256 ^ i) 0
    match ballFrom signs (s.drop 8) with
    | some c => c
    | none => sampleInBallFrom rho (2 * n) fuel

def sampleInBall (rho : ByteArray) : Poly :=
  sampleInBallFrom rho 400 12

/-! ### Keys -/

/-- The vector `NTT(v)`. -/
def nttV (v : Vec) : Vec :=
  v.map ntt

def invNttV (v : Vec) : Vec :=
  v.map invNtt

/-- Algorithm 6 (`ML-DSA.KeyGen_internal`): the public key and the secret key from the seed `ξ`. -/
def keyGen (xi : ByteArray) : ByteArray × ByteArray :=
  let seed := H (xi ++ ⟨#[dimK.toUInt8, dimL.toUInt8]⟩) 128
  let rho := seed.extract 0 32
  let rho' := seed.extract 32 96
  let key := seed.extract 96 128
  let (s1, s2) := expandS rho'
  let t := vzip padd (invNttV (matVec (expandA rho) (nttV s1))) s2
  let split := t.map fun p => (p.map fun x => (power2Round x).1, p.map fun x => (power2Round x).2)
  let t1 := split.map (·.1)
  let t0 := split.map (·.2)
  let pk := pkEncode rho t1
  let tr := H pk 64
  (pk, skEncode rho key tr s1 s2 t0)

/-- The public key of a secret key, as `ml_dsa_65_pack_pk_from_sk` returns it: `none` unless `s1`
and `s2` are within `η`, and `t0` and `tr` are those of `ρ`, `s1`, `s2`. -/
def publicKeyOfSecret (sk : ByteArray) : Option ByteArray :=
  if sk.size != skBytes then none
  else
    let k := skDecode sk
    let small (v : Vec) := v.all fun p => p.all fun x => x.natAbs ≤ eta.toNat
    let t := vzip padd (invNttV (matVec (expandA k.rho) (nttV k.s1))) k.s2
    let split := t.map fun p => (p.map fun x => (power2Round x).1, p.map fun x => (power2Round x).2)
    let pk := pkEncode k.rho (split.map (·.1))
    if small k.s1 && small k.s2 && split.map (·.2) == k.t0 && H pk 64 == k.tr then some pk else none

/-! ### Signing -/

/-- The most attempts of the rejection loop (`mldsa-native`'s `MLD_NONCE_UB`). -/
def maxAttempts : Nat :=
  13106

/-- One attempt of algorithm 7 with the nonce `κ = 5 · attempt`: `none` when it is rejected. -/
def attempt (k : Sk) (a : Array Vec) (mu rho'' : ByteArray) (kappa : Nat) : Option ByteArray :=
  let y := expandMask rho'' kappa
  let w := invNttV (matVec a (nttV y))
  let w1 := w.map fun p => p.map highBits
  let ctilde := H (mu ++ w1Encode w1) ctildeBytes
  let chat := ntt (sampleInBall ctilde)
  let times (v : Vec) : Vec := invNttV (nttV v |>.map (pmul chat))
  let cs1 := times k.s1
  let cs2 := times k.s2
  let z := (vzip padd y cs1).map fun p => p.map (modPm · q)
  let r0 := (vzip psub w cs2).map fun p => p.map lowBits
  if z.any (norm · ≥ gamma1 - beta) || r0.any (norm · ≥ gamma2 - beta) then none
  else
    let ct0 := times k.t0
    let r := vzip padd (vzip psub w cs2) ct0
    let h :=
      (Array.range dimK).map fun i =>
        (Array.range 256).map fun j => if makeHint (-ct0[i]![j]!) r[i]![j]! then (1 : Int) else 0
    let ones := h.foldl (fun n p => n + (p.foldl (· + ·.toNat) 0)) 0
    if ct0.any (norm · ≥ gamma2) || ones > omega then none else some (sigEncode ctilde z h)

/-- Algorithm 7 (`ML-DSA.Sign_internal`) on a secret key that is decoded, not checked, and the
message `M'` with the randomness `rnd`. -/
def signInternal (sk mPrime rnd : ByteArray) : Option ByteArray :=
  let k := skDecode sk
  let mu := H (k.tr ++ mPrime) 64
  let rho'' := H (k.key ++ rnd ++ mu) 64
  let a := expandA k.rho
  let rec loop (n : Nat) (attemptNo : Nat) : Option ByteArray :=
    match n with
    | 0 => none
    | n + 1 =>
      match attempt k a mu rho'' (dimL * attemptNo) with
      | some sig => some sig
      | none => loop n (attemptNo + 1)
  loop maxAttempts 0

/-- `M' = 0x00 ‖ 0x00 ‖ M`: pure mode, empty context. -/
def pure' (msg : ByteArray) : ByteArray :=
  ⟨#[0, 0]⟩ ++ msg

/-- What `near-crypto`'s `SecretKey::sign` computes given the randomness `rnd`: `none` for a secret key
that `from_raw_private_key` refuses. -/
def sign (sk msg rnd : ByteArray) : Option ByteArray :=
  (publicKeyOfSecret sk).bind fun _ => signInternal sk (pure' msg) rnd

/-! ### Verification -/

/-- Algorithm 8 (`ML-DSA.Verify_internal`) on the message `M'`. -/
def verifyInternal (pk mPrime sig : ByteArray) : Bool :=
  if pk.size != pkBytes || sig.size != sigBytes then false
  else
    match sigDecode sig with
    | none => false
    | some (ctilde, z, h) =>
      let (rho, t1) := pkDecode pk
      let mu := H (H pk 64 ++ mPrime) 64
      let chat := ntt (sampleInBall ctilde)
      let t1d := nttV (t1.map fun p => p.map (· * 2 ^ dropped))
      let w := invNttV (vzip psub (matVec (expandA rho) (nttV z)) (t1d.map (pmul chat)))
      let w1 : Vec :=
        (Array.range dimK).map fun i =>
          let hi : Poly := h[i]!
          let wi : Poly := w[i]!
          (Array.range 256).map fun j => useHint (hi[j]! != (0 : Int)) (wi[j]!)
      !z.any (norm · ≥ gamma1 - beta) && ctilde == H (mu ++ w1Encode w1) ctildeBytes

/-- `near-crypto`'s `Signature::verify` for ML-DSA-65: pure mode, empty context. -/
def verify (pk msg sig : ByteArray) : Bool :=
  verifyInternal pk (pure' msg) sig

end NearCrypto.MlDsa.Spec
