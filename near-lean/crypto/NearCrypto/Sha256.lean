import NearCrypto.Bytes
import NearCrypto.Sha2Rounds
import NearCrypto.SpecConstants

/-!
# SHA-256 (FIPS 180-4)

`Spec` follows the standard over lists: pad, split into words and blocks,
expand the schedule, run 64 rounds. `Impl` works over `ByteArray` and compresses full blocks
straight from the input with the unrolled, register-only block function of `Sha2Rounds`.
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

private def init : State256 :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

private def run (data : ByteArray) (off : Nat) (s : State256) : Nat → State256
  | 0 => s
  | n + 1 => run data (off + 64) (compress256 s data off) n

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
