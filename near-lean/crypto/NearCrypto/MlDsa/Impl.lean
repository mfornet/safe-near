import NearCrypto.Shake
import NearCrypto.MlDsa.Spec

/-!
# ML-DSA-65, the fast implementation

The same algorithms as `MlDsa.Spec`, on flat arrays of `UInt32`: a vector of `n` polynomials is an
`Array UInt32` of `256 n` coefficients in `[0, q)` (a negative coefficient is stored as `q` plus it).

* **Montgomery.** `montmul a b = a b / 2^32 mod q` from one `UInt64` product, one `UInt32` product by
  `q⁻¹ mod 2^32` and one more `UInt64` product. The zetas are kept in Montgomery form
  (`ζ^brv(i) 2^32`), so the forward NTT of a standard-form polynomial is standard; a pointwise
  product of two NTT outputs carries a factor `2^-32`, which `invNtt` removes together with the
  `1/256` (its last multiplication is by `2^64 / 256 = 41978`).
* **Roundings** work on residues in `[0, q)` without signed arithmetic: `r = f α + r0'` with
  `α = 2 γ2`; the low part is `r0'` or `r0' - α` and the special case `r - r0 = q - 1` is the case
  `high = 16`.
* **Samplers** read whole SHAKE blocks (`Shake.Impl.Xof`): 168 bytes is 56 three-byte groups and 136
  bytes is 272 nibbles, so a block never ends inside a candidate.

The encodings, the checks and the accepted inputs are the `Spec`'s; the differential tests compare
the two on seeded random keys, messages and corrupted signatures.
-/

namespace NearCrypto.MlDsa.Impl

open NearCrypto

/-! ### Arithmetic mod q -/

def q : UInt32 :=
  8380417

/-- `q⁻¹ mod 2^32`. -/
def qInv : UInt32 :=
  58728449

/-- `2 γ2`. -/
def alpha : UInt32 :=
  523776

def gamma2 : UInt32 :=
  261888

def gamma1 : UInt32 :=
  524288

def beta : UInt32 :=
  196

/-- `a b 2^-32 mod q` for `a < q` and any `b < 2^32`, in `[0, q)`. -/
@[inline]
def montmul (a b : UInt32) : UInt32 :=
  let t := a.toUInt64 * b.toUInt64
  let m := t.toUInt32 * qInv
  let r := (t >>> 32).toUInt32 + q - ((m.toUInt64 * q.toUInt64) >>> 32).toUInt32
  if r ≥ q then r - q else r

@[inline]
def addq (a b : UInt32) : UInt32 :=
  let s := a + b
  if s ≥ q then s - q else s

@[inline]
def subq (a b : UInt32) : UInt32 :=
  if a ≥ b then a - b else a + q - b

/-- `x` seen in `(-q/2, q/2]`, as an absolute value. -/
@[inline]
def absq (x : UInt32) : UInt32 :=
  if x > 4190208 then q - x else x

private def powMod (b : UInt64) : Nat → UInt64
  | 0 => 1
  | e + 1 => powMod b e * b % 8380417

private def brv8 (n : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc ||| (((n >>> i) &&& 1) <<< (7 - i))) 0

/-- `1753 ^ brv8(i) 2^32 mod q`. -/
def zetas : Array UInt32 :=
  (Array.range 256).map fun i => (powMod 1753 (brv8 i) * 4193792 % 8380417).toUInt32

/-- The forward NTT of the polynomial at coefficient `o` of `a` (algorithm 41). -/
def nttAt (a : Array UInt32) (o : Nat) : Array UInt32 :=
  Id.run do
    let mut a := a
    let mut k := 0
    for len in [128, 64, 32, 16, 8, 4, 2, 1] do
      for blk in [0:128 / len] do
        k := k + 1
        let z := zetas[k]!
        let start := o + blk * 2 * len
        for j in [start:start + len] do
          let t := montmul z a[j + len]!
          let x := a[j]!
          a := a.set! (j + len) (subq x t)
          a := a.set! j (addq x t)
    return a

/-- The inverse NTT of the polynomial at `o`, whose coefficients are products of two standard-form
NTT outputs (algorithm 42; the result is in standard form). -/
def invNttAt (a : Array UInt32) (o : Nat) : Array UInt32 :=
  Id.run do
    let mut a := a
    let mut k := 256
    for len in [1, 2, 4, 8, 16, 32, 64, 128] do
      for blk in [0:128 / len] do
        k := k - 1
        let z := q - zetas[k]!
        let start := o + blk * 2 * len
        for j in [start:start + len] do
          let t := a[j]!
          let u := a[j + len]!
          a := a.set! j (addq t u)
          a := a.set! (j + len) (montmul z (subq t u))
    for j in [o:o + 256] do
      a := a.set! j (montmul 41978 a[j]!)
    return a

/-- Transform the first `n` polynomials. -/
def nttVec (a : Array UInt32) (n : Nat) : Array UInt32 :=
  (List.range n).foldl (fun a i => nttAt a (256 * i)) a

def invNttVec (a : Array UInt32) (n : Nat) : Array UInt32 :=
  (List.range n).foldl (fun a i => invNttAt a (256 * i)) a

/-- `Â ∘ v` for the `6 × 5` matrix `a` (row-major) and the vector `v` of 5 NTT-domain polynomials:
6 polynomials carrying one factor `2^-32`. -/
def matVec (a v : Array UInt32) : Array UInt32 :=
  Id.run do
    let mut out := Array.replicate (6 * 256) 0
    for i in [0:6] do
      for j in [0:5] do
        let ao := (5 * i + j) * 256
        let vo := j * 256
        let oo := i * 256
        for c in [0:256] do
          out := out.set! (oo + c) (addq out[oo + c]! (montmul a[ao + c]! v[vo + c]!))
    return out

/-- Coefficientwise `a + b`. -/
def vadd (a b : Array UInt32) : Array UInt32 :=
  (Array.range a.size).map fun i => addq a[i]! b[i]!

def vsub (a b : Array UInt32) : Array UInt32 :=
  (Array.range a.size).map fun i => subq a[i]! b[i]!

/-- Multiply each of the `n` polynomials of `v` by the NTT-domain polynomial `c` (with one factor
`2^-32`). -/
def scale (c v : Array UInt32) (n : Nat) : Array UInt32 :=
  Id.run do
    let mut out := Array.replicate (n * 256) 0
    for i in [0:n] do
      for j in [0:256] do
        out := out.set! (i * 256 + j) (montmul c[j]! v[i * 256 + j]!)
    return out

/-! ### Rounding -/

/-- `⌊r / α⌋ + 1` if the remainder exceeds `γ2`, else `⌊r / α⌋`: the high part before the special case. -/
@[inline]
def highRaw (r : UInt32) : UInt32 :=
  let f := r / alpha
  if r - f * alpha > gamma2 then f + 1 else f

/-- `HighBits(r)` for `r` in `[0, q)`. -/
@[inline]
def highBits (r : UInt32) : UInt32 :=
  let h := highRaw r
  if h == 16 then 0 else h

/-- `|LowBits(r)|` for `r` in `[0, q)`. -/
@[inline]
def lowAbs (r : UInt32) : UInt32 :=
  let f := r / alpha
  let r0 := r - f * alpha
  if r0 > gamma2 then alpha - r0 + (if f + 1 == 16 then 1 else 0) else if f == 16 then 1 else r0

/-- Whether `LowBits(r) > 0`. -/
@[inline]
def lowPos (r : UInt32) : Bool :=
  let f := r / alpha
  let r0 := r - f * alpha
  r0 > 0 && r0 ≤ gamma2

/-- `UseHint(h, r)`. -/
@[inline]
def useHint (h : Bool) (r : UInt32) : UInt32 :=
  let r1 := highBits r
  if h then (if lowPos r then (r1 + 1) &&& 15 else (r1 + 15) &&& 15) else r1

/-- The hint polynomials for `r = w - c s2` and `rr = r + c t0`: one where the high parts differ.
(A function of its own, so that the compiler does not move the computation of its arguments into the
loop.) -/
@[noinline]
def makeHints (r rr : Array UInt32) : Array UInt32 :=
  (Array.range r.size).map fun i => if highBits rr[i]! != highBits r[i]! then (1 : UInt32) else 0

/-- `UseHint` coefficientwise. -/
@[noinline]
def useHints (h w : Array UInt32) : Array UInt32 :=
  (Array.range w.size).map fun i => useHint (h[i]! != (0 : UInt32)) w[i]!

/-! ### Packing -/

@[inline]
private def byteAt (b : ByteArray) (i : Nat) : UInt32 :=
  if i < b.size then (b.get! i).toUInt32 else 0

/-- The `bits`-bit field number `idx` (`bits ≤ 24`) of the little-endian bit string at byte `off`. -/
@[inline]
def field (b : ByteArray) (off idx bits : Nat) : UInt32 :=
  let p := off * 8 + idx * bits
  let i := p / 8
  let x :=
    byteAt b i ||| byteAt b (i + 1) <<< 8 ||| byteAt b (i + 2) <<< 16 ||| byteAt b (i + 3) <<< 24
  (x >>> (p % 8).toUInt32) &&& ((1 <<< bits.toUInt32) - 1)

/-- Append `n` values `f 0 ... f (n - 1)` of `bits` bits each, the first in the low bits. -/
@[inline]
def packWith (out : ByteArray) (n bits : Nat) (f : Nat → UInt32) : ByteArray :=
  Id.run do
    let mut out := out
    let mut acc : UInt64 := 0
    let mut nb := 0
    for i in [0:n] do
      acc := acc ||| ((f i).toUInt64 <<< nb.toUInt64)
      nb := nb + bits
      for _ in [0:3] do
        if nb ≥ 8 then
          out := out.push acc.toUInt8
          acc := acc >>> 8
          nb := nb - 8
    return out

/-! ### Sampling -/

/-- Fill `out[o + cnt ..]` with the 3-byte candidates `< q` of a 168-byte block (algorithm 14). -/
private def fillNtt (b : ByteArray) (out : Array UInt32) (o cnt : Nat) : Array UInt32 × Nat :=
  Id.run do
    let mut out := out
    let mut cnt := cnt
    for p in [0:56] do
      let z :=
        (b.get! (3 * p)).toUInt32 ||| (b.get! (3 * p + 1)).toUInt32 <<< 8 |||
          ((b.get! (3 * p + 2)).toUInt32 &&& 0x7f) <<< 16
      if z < q && cnt < 256 then
        out := out.set! (o + cnt) z
        cnt := cnt + 1
    return (out, cnt)

private def sampleNtt (seed : ByteArray) (out : Array UInt32) (o : Nat) : Array UInt32 :=
  let rec go (x : Shake.Impl.Xof) (out : Array UInt32) (cnt : Nat) : Nat → Array UInt32
    | 0 => out
    | fuel + 1 =>
      if cnt ≥ 256 then out
      else
        let (b, x) := x.block
        let (out, cnt) := fillNtt b out o cnt
        go x out cnt fuel
  go (Shake.Impl.Xof.init 168 seed) out 0 64

/-- `Â` (algorithm 32): the 30 polynomials `A[i][j]` in row-major order, in the NTT domain. -/
def expandA (rho : ByteArray) : Array UInt32 :=
  Id.run do
    let mut out := Array.replicate (30 * 256) 0
    for i in [0:6] do
      for j in [0:5] do
        out := sampleNtt (rho ++ ⟨#[j.toUInt8, i.toUInt8]⟩) out ((5 * i + j) * 256)
    return out

/-- `4 - b` modulo `q` for a nibble `b < 9`. -/
@[inline]
private def etaCoeff (b : UInt32) : UInt32 :=
  if b ≤ 4 then 4 - b else q + 4 - b

private def fillBounded (b : ByteArray) (out : Array UInt32) (o cnt : Nat) : Array UInt32 × Nat :=
  Id.run do
    let mut out := out
    let mut cnt := cnt
    for p in [0:272] do
      let byte := (b.get! (p / 2)).toUInt32
      let nib := if p % 2 == 0 then byte &&& 15 else byte >>> 4
      if nib < 9 && cnt < 256 then
        out := out.set! (o + cnt) (etaCoeff nib)
        cnt := cnt + 1
    return (out, cnt)

private def sampleBounded (seed : ByteArray) (out : Array UInt32) (o : Nat) : Array UInt32 :=
  let rec go (x : Shake.Impl.Xof) (out : Array UInt32) (cnt : Nat) : Nat → Array UInt32
    | 0 => out
    | fuel + 1 =>
      if cnt ≥ 256 then out
      else
        let (b, x) := x.block
        let (out, cnt) := fillBounded b out o cnt
        go x out cnt fuel
  go (Shake.Impl.Xof.init 136 seed) out 0 64

private def le16 (x : Nat) : ByteArray :=
  ⟨#[x.toUInt8, (x / 256).toUInt8]⟩

/-- `s1` (5 polynomials) and `s2` (6) from `ρ'` (algorithm 33). -/
def expandS (rho : ByteArray) : Array UInt32 × Array UInt32 :=
  Id.run do
    let mut s1 := Array.replicate (5 * 256) 0
    let mut s2 := Array.replicate (6 * 256) 0
    for r in [0:5] do
      s1 := sampleBounded (rho ++ le16 r) s1 (r * 256)
    for r in [0:6] do
      s2 := sampleBounded (rho ++ le16 (r + 5)) s2 (r * 256)
    return (s1, s2)

/-- `y` (algorithm 34): the coefficient `γ1 - v` of a 20-bit field `v`, modulo `q`. -/
def expandMask (rho : ByteArray) (kappa : Nat) : Array UInt32 :=
  Id.run do
    let mut y := Array.replicate (5 * 256) 0
    for r in [0:5] do
      let v := Shake.Impl.shake256 (rho ++ le16 (kappa + r)) 640
      for i in [0:256] do
        let f := field v 0 i 20
        y := y.set! (r * 256 + i) (if f ≤ gamma1 then gamma1 - f else q + gamma1 - f)
    return y

/-- The position in the SHAKE256 stream of `SampleInBall`: the current block and the next byte of it. -/
private structure Ball where
  block : ByteArray
  pos : Nat
  xof : Shake.Impl.Xof

/-- The next byte of the stream that is at most `i`, giving up after `fuel` bytes. -/
private def nextAtMost (i : Nat) (s : Ball) : Nat → Nat × Ball
  | 0 => (0, s)
  | fuel + 1 =>
    if s.pos ≥ 136 then
      let (b, x) := s.xof.block
      nextAtMost i ⟨b, 0, x⟩ fuel
    else
      let j := (s.block.get! s.pos).toNat
      if j ≤ i then (j, { s with pos := s.pos + 1 })
      else nextAtMost i { s with pos := s.pos + 1 } fuel

private def ballLoop (signs : UInt64) (i : Nat) (c : Array UInt32) (s : Ball) : Nat → Array UInt32
  | 0 => c
  | fuel + 1 =>
    if i ≥ 256 then c
    else
      let (j, s) := nextAtMost i s 100000
      let c := c.set! i c[j]!
      let c := c.set! j (if (signs >>> (i + 49 - 256).toUInt64) &&& 1 == 1 then q - 1 else 1)
      ballLoop signs (i + 1) c s fuel

/-- `SampleInBall` (algorithm 29): a polynomial with 49 coefficients `±1` (`q - 1` for `-1`). -/
def sampleInBall (ctilde : ByteArray) : Array UInt32 :=
  let (b, x) := (Shake.Impl.Xof.init 136 ctilde).block
  ballLoop (le64 b 0) (256 - 49) (Array.replicate 256 0) ⟨b, 8, x⟩ 49

/-! ### Encodings -/

/-- The hint polynomials `h` (6 polynomials of 0/1) of the 61 bytes `y`, or `none` if malformed. -/
def hintUnpack (y : ByteArray) (off : Nat) : Option (Array UInt32) :=
  Id.run do
    let mut h := Array.replicate (6 * 256) 0
    let mut index := 0
    for i in [0:6] do
      let cnt := (y.get! (off + 55 + i)).toNat
      if cnt < index || cnt > 55 then
        return none
      let first := index
      while index < cnt do
        if index > first && (y.get! (off + index - 1)) ≥ y.get! (off + index) then
          return none
        h := h.set! (i * 256 + (y.get! (off + index)).toNat) 1
        index := index + 1
    for j in [index:55] do
      if y.get! (off + j) != 0 then
        return none
    return some h

/-- The 61 bytes of the hint (`h` has at most 55 ones). -/
def hintPack (h : Array UInt32) : ByteArray :=
  Id.run do
    let mut idx := ByteArray.emptyWithCapacity 61
    let mut counts := ByteArray.emptyWithCapacity 6
    for i in [0:6] do
      for j in [0:256] do
        if h[i * 256 + j]! != 0 then
          idx := idx.push j.toUInt8
      counts := counts.push idx.size.toUInt8
    return idx ++ zeros (55 - idx.size) ++ counts

/-- `w1` as 4-bit fields. -/
def w1Pack (w1 : Array UInt32) : ByteArray :=
  packWith (ByteArray.emptyWithCapacity 768) (6 * 256) 4 fun i => w1[i]!

/-- The fields `bits` bits wide of `n` polynomials at byte `off`, as `f` maps each. -/
@[inline]
def unpackPolys (b : ByteArray) (off n bits : Nat) (f : UInt32 → UInt32) : Array UInt32 :=
  (Array.range (n * 256)).map fun i => f (field b off i bits)

/-- Pack `n` polynomials with `bits`-bit fields given by `f` of each coefficient. -/
@[inline]
def packPolys (a : Array UInt32) (n bits : Nat) (f : UInt32 → UInt32) : ByteArray :=
  packWith (ByteArray.emptyWithCapacity (n * 32 * bits)) (n * 256) bits fun i => f a[i]!

/-- The nibble `η - s` of a coefficient `s` stored modulo `q`. -/
@[inline]
private def nibble (s : UInt32) : UInt32 :=
  if s ≤ 4 then 4 - s else 4 + q - s

/-- The 13-bit field `2^12 - t0` of `t0` modulo `q`. -/
@[inline]
private def t0Field (t : UInt32) : UInt32 :=
  if t ≤ 4096 then 4096 - t else 4096 + q - t

/-- `t0` modulo `q` from its 13-bit field. -/
@[inline]
private def t0OfField (z : UInt32) : UInt32 :=
  if z ≤ 4096 then 4096 - z else q + 4096 - z

/-! ### Keys -/

/-- `t = Â s1 + s2`: `t1` and the 13-bit `t0` fields, with the encoded public key and `tr`. -/
private def derive (rho : ByteArray) (s1 s2 : Array UInt32) : ByteArray × ByteArray × ByteArray :=
  let t := vadd (invNttVec (matVec (expandA rho) (nttVec s1 5)) 6) s2
  let t1 := t.map fun (r : UInt32) => if (r &&& 8191) > 4096 then (r >>> 13) + 1 else r >>> 13
  let t0 :=
    t.map fun (r : UInt32) =>
      if (r &&& 8191) > 4096 then 12288 - (r &&& 8191) else 4096 - (r &&& 8191)
  let pk := packWith rho 1536 10 fun i => t1[i]!
  (pk, Shake.Impl.shake256 pk 64, packWith ByteArray.empty 1536 13 fun i => t0[i]!)

/-- `ML-DSA.KeyGen_internal` (algorithm 6): the public and secret keys from the seed `ξ`. -/
def keyGen (xi : ByteArray) : ByteArray × ByteArray :=
  let seed := Shake.Impl.shake256 (xi ++ ⟨#[6, 5]⟩) 128
  let rho := seed.extract 0 32
  let (s1, s2) := expandS (seed.extract 32 96)
  let (pk, tr, t0) := derive rho s1 s2
  let nib (a : Array UInt32) (n : Nat) := packPolys a n 4 nibble
  (pk, rho ++ seed.extract 96 128 ++ tr ++ nib s1 5 ++ nib s2 6 ++ t0)

/-- The decoded parts of a secret key (nothing checked): `ρ`, `K`, `tr`, `s1`, `s2`, `t0` modulo `q`
and whether every nibble of `s1` and `s2` is at most 8. -/
private def secretParts (sk : ByteArray) :
    ByteArray × ByteArray × ByteArray × Array UInt32 × Array UInt32 × Array UInt32 × Bool :=
  let eta (f : UInt32) : UInt32 := etaCoeff f
  let s1 := unpackPolys sk 128 5 4 eta
  let s2 := unpackPolys sk (128 + 5 * 128) 6 4 eta
  let ok := (List.range (11 * 256)).all fun i => field sk 128 i 4 ≤ 8
  (sk.extract 0 32, sk.extract 32 64, sk.extract 64 128, s1, s2,
    unpackPolys sk (128 + 11 * 128) 6 13 t0OfField, ok)

/-- Whether `sk` is a secret key that AWS-LC accepts, with its public key. -/
def publicKeyOfSecret (sk : ByteArray) : Option ByteArray :=
  if sk.size != 4032 then none
  else
    let (rho, _, tr, s1, s2, _, ok) := secretParts sk
    if !ok then none
    else
      let (pk, tr', t0) := derive rho s1 s2
      if tr' == tr && t0 == sk.extract (128 + 11 * 128) 4032 then some pk else none

/-! ### Signing -/

/-- One attempt of algorithm 7. -/
private def attempt (a s1h s2h t0h : Array UInt32) (mu rho'' : ByteArray) (kappa : Nat) :
    Option ByteArray :=
  let y := expandMask rho'' kappa
  let w := invNttVec (matVec a (nttVec y 5)) 6
  let w1 := w.map highBits
  let ctilde := Shake.Impl.shake256 (mu ++ w1Pack w1) 48
  let chat := nttAt (sampleInBall ctilde) 0
  let cs1 := invNttVec (scale chat s1h 5) 5
  let z := vadd y cs1
  if z.any fun x => absq x ≥ gamma1 - beta then none
  else
    let cs2 := invNttVec (scale chat s2h 6) 6
    let r := vsub w cs2
    if r.any fun x => lowAbs x ≥ gamma2 - beta then none
    else
      let ct0 := invNttVec (scale chat t0h 6) 6
      if ct0.any fun x => absq x ≥ gamma2 then none
      else
        let rr := vadd r ct0
        let h := makeHints r rr
        if h.foldl (· + ·) 0 > 55 then none
        else
          let zf := fun x : UInt32 => if x ≤ gamma1 then gamma1 - x else gamma1 + q - x
          some (ctilde ++ packPolys z 5 20 zf ++ hintPack h)

/-- `ML-DSA.Sign_internal` (algorithm 7) on a decoded secret key. -/
def signInternal (sk mPrime rnd : ByteArray) : Option ByteArray :=
  let (rho, key, tr, s1, s2, t0, _) := secretParts sk
  let mu := Shake.Impl.shake256 (tr ++ mPrime) 64
  let rho'' := Shake.Impl.shake256 (key ++ rnd ++ mu) 64
  let a := expandA rho
  let s1h := nttVec s1 5
  let s2h := nttVec s2 6
  let t0h := nttVec t0 6
  let rec loop : Nat → Nat → Option ByteArray
    | 0, _ => none
    | n + 1, attemptNo =>
      match attempt a s1h s2h t0h mu rho'' (5 * attemptNo) with
      | some sig => some sig
      | none => loop n (attemptNo + 1)
  loop Spec.maxAttempts 0

def pure' (msg : ByteArray) : ByteArray :=
  ⟨#[0, 0]⟩ ++ msg

/-- What `near-crypto`'s `SecretKey::sign` computes given the randomness `rnd`. -/
def sign (sk msg rnd : ByteArray) : Option ByteArray :=
  (publicKeyOfSecret sk).bind fun _ => signInternal sk (pure' msg) rnd

/-! ### Verification -/

/-- `ML-DSA.Verify_internal` (algorithm 8) on `M'`. -/
def verifyInternal (pk mPrime sig : ByteArray) : Bool :=
  if pk.size != 1952 || sig.size != 3309 then false
  else
    match hintUnpack sig (48 + 5 * 640) with
    | none => false
    | some h =>
      let z := unpackPolys sig 48 5 20 fun f => if f ≤ gamma1 then gamma1 - f else q + gamma1 - f
      if z.any fun x => absq x ≥ gamma1 - beta then false
      else
        let ctilde := sig.extract 0 48
        let mu := Shake.Impl.shake256 (Shake.Impl.shake256 pk 64 ++ mPrime) 64
        let chat := nttAt (sampleInBall ctilde) 0
        let t1d := nttVec (unpackPolys pk 32 6 10 fun t => t <<< 13) 6
        let az := matVec (expandA (pk.extract 0 32)) (nttVec z 5)
        let w := invNttVec (vsub az (scale chat t1d 6)) 6
        let w1 := useHints h w
        ctilde == Shake.Impl.shake256 (mu ++ w1Pack w1) 48

/-- `near-crypto`'s `Signature::verify` for ML-DSA-65: pure mode, empty context. -/
def verify (pk msg sig : ByteArray) : Bool :=
  verifyInternal pk (pure' msg) sig

end NearCrypto.MlDsa.Impl

namespace NearCrypto

/-- `near-crypto`'s ML-DSA-65 `Signature::verify`: a 1952-byte key, a 3309-byte signature, pure mode
with an empty context. -/
def mlDsa65Verify (pk msg sig : ByteArray) : Bool :=
  MlDsa.Impl.verify pk msg sig

/-- The public and the 4032-byte secret key of the 32-byte seed (`near-crypto`'s `ml_dsa_65_from_seed`). -/
def mlDsa65KeyGen (seed : ByteArray) : Option (ByteArray × ByteArray) :=
  if seed.size == 32 then some (MlDsa.Impl.keyGen seed) else none

/-- The public key of a 4032-byte secret key, `none` for a key `near-crypto` refuses (`SecretKey::from_str`). -/
def mlDsa65PublicKey (sk : ByteArray) : Option ByteArray :=
  MlDsa.Impl.publicKeyOfSecret sk

/-- A signature of `msg` given 32 bytes of randomness (`near-crypto` draws them at random). -/
def mlDsa65Sign (sk msg rnd : ByteArray) : Option ByteArray :=
  if rnd.size == 32 then MlDsa.Impl.sign sk msg rnd else none

end NearCrypto
