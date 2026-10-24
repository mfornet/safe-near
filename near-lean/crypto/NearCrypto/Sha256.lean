import NearCrypto.Bytes
import NearCrypto.SpecConstants

/-!
# SHA-256 (FIPS 180-4)

`Spec` follows the standard over lists: pad, split into words and blocks,
expand the schedule, run 64 rounds. `Impl` works over `ByteArray` with
unboxed `UInt32` registers and compresses full blocks straight from the input.
-/

namespace NearCrypto.Sha256

/-! ### Spec -/

namespace Spec

/-- Rotate right. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- The round constants: cube roots of the first 64 primes. -/
def K : List UInt32 :=
  (SpecConstants.primes 64).map fun p => (SpecConstants.rootBits 3 32 p).toUInt32

/-- The initial hash value: square roots of the first 8 primes. -/
def H0 : List UInt32 :=
  (SpecConstants.primes 8).map fun p => (SpecConstants.rootBits 2 32 p).toUInt32

/-- The message followed by `1`, zeros and the bit length, a multiple of 64 bytes. -/
def pad (m : List UInt8) : List UInt8 :=
  let bits := 8 * m.length
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    (List.range 8).reverse.map fun i => UInt8.ofNat (bits / 256 ^ i)

/-- Big-endian words. -/
def words : List UInt8 → List UInt32
  | a :: b :: c :: d :: r =>
    (a.toUInt32 <<< 24 ||| b.toUInt32 <<< 16 ||| c.toUInt32 <<< 8 ||| d.toUInt32) :: words r
  | _ => []

/-- The 64-word message schedule of a 16-word block. -/
def schedule (blk : List UInt32) : List UInt32 :=
  (List.range 48).foldl
    (fun w _ =>
      let n := w.length
      let x := w.getD (n - 15) 0
      let y := w.getD (n - 2) 0
      let s0 := rotr x 7 ^^^ rotr x 18 ^^^ x >>> 3
      let s1 := rotr y 17 ^^^ rotr y 19 ^^^ y >>> 10
      w ++ [w.getD (n - 16) 0 + s0 + w.getD (n - 7) 0 + s1])
    blk

/-- One round on `[a, b, c, d, e, f, g, h]`. -/
def round (s : List UInt32) (k w : UInt32) : List UInt32 :=
  match s with
  | [a, b, c, d, e, f, g, h] =>
    let t1 := h + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + k + w
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    [t1 + t2, a, b, c, d + t1, e, f, g]
  | _ => s

/-- Compress one block into the hash value. -/
def compress (hv : List UInt32) (blk : List UInt32) : List UInt32 :=
  let out := ((schedule blk).zip K).foldl (fun s (w, k) => round s k w) hv
  hv.zipWith (· + ·) out

/-- SHA-256 of a byte list. -/
def hashList (m : List UInt8) : List UInt8 :=
  let ws := words (pad m)
  let hv := (SpecConstants.chunks 16 ws).foldl compress H0
  hv.flatMap fun (x : UInt32) =>
    [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- SHA-256 of `m`. -/
def hash (m : ByteArray) : ByteArray :=
  ⟨(hashList m.toList).toArray⟩

end Spec

/-! ### Impl -/

namespace Impl

private def K : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The eight chaining words. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

private def init : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

@[inline]
private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Append the schedule words `16 + (k - n) .. 16 + k` to `w`. -/
private def expand (w : Array UInt32) : Nat → Array UInt32
  | 0 => w
  | n + 1 =>
    let i := w.size
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ x >>> 3
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ y >>> 10
    expand (w.push (w[i - 16]! + s0 + w[i - 7]! + s1)) n

private def load (data : ByteArray) (off : Nat) : Nat → Array UInt32 → Array UInt32
  | 0, w => w
  | n + 1, w => load data (off + 4) n (w.push (be32 data off))

/-- Rounds `64 - n .. 63`. -/
private def rounds (w : Array UInt32) (a b c d e f g h : UInt32) : Nat → State
  | 0 => ⟨a, b, c, d, e, f, g, h⟩
  | n + 1 =>
    let i := 63 - n
    let t1 :=
      h + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + K[i]! + w[i]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    rounds w (t1 + t2) a b c (d + t1) e f g n

private def compress (s : State) (data : ByteArray) (off : Nat) : State :=
  let w := expand (load data off 16 (Array.mkEmpty 64)) 48
  let r := rounds w s.a s.b s.c s.d s.e s.f s.g s.h 64
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

private def run (data : ByteArray) (off : Nat) (s : State) : Nat → State
  | 0 => s
  | n + 1 => run data (off + 64) (compress s data off) n

/-- SHA-256 of `m`. -/
def hash (m : ByteArray) : ByteArray :=
  let full := m.size / 64
  let s := run m 0 init full
  let rest := m.size % 64
  let zeroCount := (119 - rest) % 64
  let tail := ((m.extract (64 * full) m.size).push 0x80 ++ zeros zeroCount)
  let tail := pushBe64 tail (8 * m.size).toUInt64
  let s := run tail 0 s (tail.size / 64)
  pushBe32
    (pushBe32
      (pushBe32
        (pushBe32 (pushBe32 (pushBe32 (pushBe32 (pushBe32 ByteArray.empty s.a) s.b) s.c) s.d) s.e)
        s.f)
      s.g)
    s.h

end Impl

end NearCrypto.Sha256

namespace NearCrypto

/-- SHA-256 of `m`. -/
def sha256 (m : ByteArray) : ByteArray :=
  Sha256.Impl.hash m

end NearCrypto
