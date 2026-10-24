import NearCrypto.Bytes
import NearCrypto.SpecConstants

/-!
# SHA-512 (FIPS 180-4)

`Spec` follows the standard over lists; `Impl` works over `ByteArray` with
unboxed `UInt64` registers.
-/

namespace NearCrypto.Sha512

/-! ### Spec -/

namespace Spec

/-- Rotate right. -/
def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- The round constants: cube roots of the first 80 primes. -/
def K : List UInt64 :=
  (SpecConstants.primes 80).map fun p => (SpecConstants.rootBits 3 64 p).toUInt64

/-- The initial hash value: square roots of the first 8 primes. -/
def H0 : List UInt64 :=
  (SpecConstants.primes 8).map fun p => (SpecConstants.rootBits 2 64 p).toUInt64

/-- The message followed by `1`, zeros and the 128-bit bit length, a multiple of 128 bytes. -/
def pad (m : List UInt8) : List UInt8 :=
  let bits := 8 * m.length
  m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++
    (List.range 16).reverse.map fun i => UInt8.ofNat (bits / 256 ^ i)

/-- Big-endian words. -/
def words : List UInt8 → List UInt64
  | a :: b :: c :: d :: e :: f :: g :: h :: r =>
    (a.toUInt64 <<< 56 ||| b.toUInt64 <<< 48 ||| c.toUInt64 <<< 40 ||| d.toUInt64 <<< 32 |||
        e.toUInt64 <<< 24 |||
        f.toUInt64 <<< 16 |||
        g.toUInt64 <<< 8 |||
        h.toUInt64) ::
      words r
  | _ => []

/-- The 80-word message schedule of a 16-word block. -/
def schedule (blk : List UInt64) : List UInt64 :=
  (List.range 64).foldl
    (fun w _ =>
      let n := w.length
      let x := w.getD (n - 15) 0
      let y := w.getD (n - 2) 0
      let s0 := rotr x 1 ^^^ rotr x 8 ^^^ x >>> 7
      let s1 := rotr y 19 ^^^ rotr y 61 ^^^ y >>> 6
      w ++ [w.getD (n - 16) 0 + s0 + w.getD (n - 7) 0 + s1])
    blk

/-- One round on `[a, b, c, d, e, f, g, h]`. -/
def round (s : List UInt64) (k w : UInt64) : List UInt64 :=
  match s with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := h + (rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41) + ((e &&& f) ^^^ (~~~e &&& g)) + k + w
    let t2 := (rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    [t1 + t2, a, b, c, d + t1, e, f, g]
  | _ => s

/-- Compress one block into the hash value. -/
def compress (hv : List UInt64) (blk : List UInt64) : List UInt64 :=
  let out := ((schedule blk).zip K).foldl (fun s (w, k) => round s k w) hv
  hv.zipWith (· + ·) out

/-- SHA-512 of a byte list. -/
def hashList (m : List UInt8) : List UInt8 :=
  let ws := words (pad m)
  let hv := (SpecConstants.chunks 16 ws).foldl compress H0
  hv.flatMap fun (x : UInt64) =>
    (List.range 8).reverse.map fun i => (x >>> (8 * i).toUInt64).toUInt8

/-- SHA-512 of `m`. -/
def hash (m : ByteArray) : ByteArray :=
  ⟨(hashList m.toList).toArray⟩

end Spec

/-! ### Impl -/

namespace Impl

private def K : Array UInt64 :=
  #[0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

/-- The eight chaining words. -/
structure State where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  e : UInt64
  f : UInt64
  g : UInt64
  h : UInt64

private def init : State :=
  ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

@[inline]
private def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- Append `n` more schedule words to `w`. -/
private def expand (w : Array UInt64) : Nat → Array UInt64
  | 0 => w
  | n + 1 =>
    let i := w.size
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 1 ^^^ rotr x 8 ^^^ x >>> 7
    let s1 := rotr y 19 ^^^ rotr y 61 ^^^ y >>> 6
    expand (w.push (w[i - 16]! + s0 + w[i - 7]! + s1)) n

private def load (data : ByteArray) (off : Nat) : Nat → Array UInt64 → Array UInt64
  | 0, w => w
  | n + 1, w => load data (off + 8) n (w.push (be64 data off))

/-- Rounds `80 - n .. 79`. -/
private def rounds (w : Array UInt64) (a b c d e f g h : UInt64) : Nat → State
  | 0 => ⟨a, b, c, d, e, f, g, h⟩
  | n + 1 =>
    let i := 79 - n
    let t1 :=
      h + (rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41) + ((e &&& f) ^^^ (~~~e &&& g)) + K[i]! + w[i]!
    let t2 := (rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    rounds w (t1 + t2) a b c (d + t1) e f g n

private def compress (s : State) (data : ByteArray) (off : Nat) : State :=
  let w := expand (load data off 16 (Array.mkEmpty 80)) 64
  let r := rounds w s.a s.b s.c s.d s.e s.f s.g s.h 80
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

private def run (data : ByteArray) (off : Nat) (s : State) : Nat → State
  | 0 => s
  | n + 1 => run data (off + 128) (compress s data off) n

/-- SHA-512 of `m`. -/
def hash (m : ByteArray) : ByteArray :=
  let full := m.size / 128
  let s := run m 0 init full
  let rest := m.size % 128
  let tail := (m.extract (128 * full) m.size).push 0x80 ++ zeros ((239 - rest) % 128)
  let tail := pushBe64 (pushBe64 tail 0) (8 * m.size).toUInt64
  let s := run tail 0 s (tail.size / 128)
  pushBe64
    (pushBe64
      (pushBe64
        (pushBe64 (pushBe64 (pushBe64 (pushBe64 (pushBe64 ByteArray.empty s.a) s.b) s.c) s.d) s.e)
        s.f)
      s.g)
    s.h

end Impl

end NearCrypto.Sha512

namespace NearCrypto

/-- SHA-512 of `m`. -/
def sha512 (m : ByteArray) : ByteArray :=
  Sha512.Impl.hash m

end NearCrypto
