import NearCrypto.Bytes
import NearCrypto.Sha2Rounds
import NearCrypto.SpecConstants

/-!
# SHA-512 (FIPS 180-4)

`Spec` follows the standard over lists; `Impl` works over `ByteArray` with the unrolled
block function of `Sha2Rounds`.
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

private def init : State512 :=
  ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

private def run (data : ByteArray) (off : Nat) (s : State512) : Nat → State512
  | 0 => s
  | n + 1 => run data (off + 128) (compress512 s data off) n

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
