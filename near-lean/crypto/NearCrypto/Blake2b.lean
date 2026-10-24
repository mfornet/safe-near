import NearCrypto.Bytes
import NearCrypto.Blake2bRounds
import NearCrypto.Sha512

/-!
# BLAKE2b (RFC 7693)

Unkeyed, with a digest length of 1 to 64 bytes. `near-crypto`'s VRF hashes with BLAKE2b-256
(`Blake2bVar::new(32)`) and BLAKE2b-512 (`Blake2b512`); the digest length is part of the
parameter block, so the 32-byte digest is not a prefix of the 64-byte one. `Spec` keeps the
sixteen working words in a list; `Impl` is the unrolled compression function of `Blake2bRounds`
on unboxed registers.
-/

namespace NearCrypto.Blake2b

/-- The message word schedule of the ten distinct rounds (rounds 10 and 11 repeat 0 and 1). -/
def sigma : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Rotate right. -/
@[inline]
def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- The initial hash value: the SHA-512 one. -/
def iv : List UInt64 :=
  Sha512.Spec.H0

/-- The little-endian words of block `i` of the message, zero padded to 128 bytes. -/
def blockWords (m : ByteArray) (off : Nat) : List UInt64 :=
  (List.range 16).map fun i =>
    (List.range 8).foldr
      (fun j acc =>
        acc <<< 8 ||| (if off + 8 * i + j < m.size then m.get! (off + 8 * i + j) else 0).toUInt64)
      0

/-- The first `nn` bytes of the little-endian words of the state. -/
def output (h : List UInt64) (nn : Nat) : ByteArray :=
  (h.foldl pushLe64 ByteArray.empty).extract 0 nn

/-- The initial state for a digest of `nn` bytes (no key). -/
def init (nn : Nat) : List UInt64 :=
  match iv with
  | h0 :: t => (h0 ^^^ 0x01010000 ^^^ nn.toUInt64) :: t
  | [] => []

/-! ### Spec -/

namespace Spec

/-- The mixing function `G` on words `a b c d` of `v` with message words `x y`. -/
def mix (v : List UInt64) (a b c d : Nat) (x y : UInt64) : List UInt64 :=
  let va := v.getD a 0 + v.getD b 0 + x
  let vd := rotr (v.getD d 0 ^^^ va) 32
  let vc := v.getD c 0 + vd
  let vb := rotr (v.getD b 0 ^^^ vc) 24
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 63
  ((((v.set a va).set b vb).set c vc).set d vd)

/-- One round: the eight mixes of schedule row `r`. -/
def round (v : List UInt64) (w : List UInt64) (r : Nat) : List UInt64 :=
  let s := sigma.getD (r % 10) []
  let g (v : List UInt64) (a b c d i : Nat) : List UInt64 :=
    mix v a b c d (w.getD (s.getD (2 * i) 0) 0) (w.getD (s.getD (2 * i + 1) 0) 0)
  let v := g v 0 4 8 12 0
  let v := g v 1 5 9 13 1
  let v := g v 2 6 10 14 2
  let v := g v 3 7 11 15 3
  let v := g v 0 5 10 15 4
  let v := g v 1 6 11 12 5
  let v := g v 2 7 8 13 6
  g v 3 4 9 14 7

/-- The compression function `F`: state, block words, byte counter, last-block flag. -/
def compress (h : List UInt64) (w : List UInt64) (t : UInt64) (last : Bool) : List UInt64 :=
  let v := h ++ iv
  let v := v.set 12 (v.getD 12 0 ^^^ t)
  let v := if last then v.set 14 (~~~v.getD 14 0) else v
  let v := (List.range 12).foldl (fun v r => round v w r) v
  (List.range 8).map fun i => h.getD i 0 ^^^ v.getD i 0 ^^^ v.getD (i + 8) 0

/-- BLAKE2b with a digest of `nn` bytes (1 to 64) of `m`, unkeyed. The last block is the final
nonempty one, or the empty block for an empty message. -/
def hash (nn : Nat) (m : ByteArray) : ByteArray :=
  let blocks := if m.size == 0 then 1 else (m.size + 127) / 128
  output
    ((List.range blocks).foldl
      (fun h i =>
        let last := i + 1 == blocks
        let t := if last then m.size else 128 * (i + 1)
        compress h (blockWords m (128 * i)) t.toUInt64 last)
      (init nn))
    nn

end Spec

/-! ### Impl -/

namespace Impl

private def init (nn : Nat) : State512 :=
  ⟨0x6a09e667f3bcc908 ^^^ 0x01010000 ^^^ nn.toUInt64, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179⟩

private def run (data : ByteArray) (off : Nat) (s : State512) : Nat → State512
  | 0 => s
  | n + 1 => run data (off + 128) (compressBlake2b s data off (off + 128).toUInt64 false) n

/-- BLAKE2b with a digest of `nn` bytes (1 to 64) of `m`, unkeyed. -/
def hash (nn : Nat) (m : ByteArray) : ByteArray :=
  let blocks := if m.size == 0 then 1 else (m.size + 127) / 128
  let s := run m 0 (init nn) (blocks - 1)
  let tail := m.extract (128 * (blocks - 1)) m.size
  let tail := tail ++ zeros (128 - tail.size)
  let s := compressBlake2b s tail 0 m.size.toUInt64 true
  let all :=
    pushLe64
      (pushLe64
        (pushLe64
          (pushLe64 (pushLe64 (pushLe64 (pushLe64 (pushLe64 ByteArray.empty s.a) s.b) s.c) s.d) s.e)
          s.f)
        s.g)
      s.h
  all.extract 0 nn

end Impl

end NearCrypto.Blake2b

namespace NearCrypto

/-- BLAKE2b-256. -/
def blake2b256 (m : ByteArray) : ByteArray :=
  Blake2b.Impl.hash 32 m

/-- BLAKE2b-512. -/
def blake2b512 (m : ByteArray) : ByteArray :=
  Blake2b.Impl.hash 64 m

end NearCrypto
