import NearCrypto.Bytes
import NearCrypto.SpecConstants

/-!
# RIPEMD-160

Dobbertin, Bosselaers and Preneel's original specification: two parallel lines
of 80 steps over the little-endian words of each 64-byte block. `Spec` keeps
the five-word line state in a list and takes the word and rotation tables as
lists; `Impl` runs both lines in one tail-recursive loop over unboxed `UInt32`
registers.
-/

namespace NearCrypto.Ripemd160

/-- Message word order of the left line. -/
def r : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2,
    14, 11, 8, 3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4, 13,
    3, 7, 15, 14, 5, 6, 2, 4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- Message word order of the right line. -/
def r' : List Nat :=
  [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12,
    4, 9, 1, 2, 15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5,
    12, 2, 13, 9, 7, 10, 14, 12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- Rotation amounts of the left line. -/
def s : List Nat :=
  [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9,
    11, 7, 13, 12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14, 15,
    9, 8, 9, 14, 5, 6, 8, 6, 5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- Rotation amounts of the right line. -/
def s' : List Nat :=
  [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7,
    6, 15, 13, 11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14, 6,
    14, 6, 9, 12, 9, 12, 5, 15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

/-- The nonlinear function of round group `g`. -/
@[inline]
def f (g : Nat) (x y z : UInt32) : UInt32 :=
  match g with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => x ^^^ (y ||| ~~~z)

/-- Left-line constants. -/
@[inline]
def k (g : Nat) : UInt32 :=
  match g with
  | 0 => 0x00000000
  | 1 => 0x5A827999
  | 2 => 0x6ED9EBA1
  | 3 => 0x8F1BBCDC
  | _ => 0xA953FD4E

/-- Right-line constants. -/
@[inline]
def k' (g : Nat) : UInt32 :=
  match g with
  | 0 => 0x50A28BE6
  | 1 => 0x5C4DD124
  | 2 => 0x6D703EF3
  | 3 => 0x7A6D76E9
  | _ => 0x00000000

/-- Rotate left. -/
@[inline]
def rol (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- The initial chaining value. -/
def H0 : List UInt32 :=
  [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-! ### Spec -/

namespace Spec

/-- One step of a line on `[A, B, C, D, E]`. -/
def step (st : List UInt32) (fv kv x : UInt32) (sh : Nat) : List UInt32 :=
  match st with
  | [a, b, c, d, e] =>
    let t := rol (a + fv + x + kv) sh.toUInt32 + e
    [e, t, b, rol c 10, d]
  | _ => st

/-- Little-endian words. -/
def words : List UInt8 → List UInt32
  | a :: b :: c :: d :: rest =>
    (a.toUInt32 ||| b.toUInt32 <<< 8 ||| c.toUInt32 <<< 16 ||| d.toUInt32 <<< 24) :: words rest
  | _ => []

/-- The message followed by `1`, zeros and the 64-bit little-endian bit length. -/
def pad (m : List UInt8) : List UInt8 :=
  let bits := 8 * m.length
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    (List.range 8).map fun i => UInt8.ofNat (bits / 256 ^ i)

/-- Compress one block of 16 words. -/
def compress (h : List UInt32) (x : List UInt32) : List UInt32 :=
  let left :=
    (List.range 80).foldl
      (fun st j =>
        step st (f (j / 16) (st.getD 1 0) (st.getD 2 0) (st.getD 3 0)) (k (j / 16))
          (x.getD (r.getD j 0) 0) (s.getD j 0))
      h
  let right :=
    (List.range 80).foldl
      (fun st j =>
        step st (f (4 - j / 16) (st.getD 1 0) (st.getD 2 0) (st.getD 3 0)) (k' (j / 16))
          (x.getD (r'.getD j 0) 0) (s'.getD j 0))
      h
  match h, left, right with
  | [h0, h1, h2, h3, h4], [a, b, c, d, e], [a', b', c', d', e'] =>
    [h1 + c + d', h2 + d + e', h3 + e + a', h4 + a + b', h0 + b + c']
  | _, _, _ => h

/-- RIPEMD-160 of a byte list. -/
def hashList (m : List UInt8) : List UInt8 :=
  let ws := words (pad m)
  let hv := (SpecConstants.chunks 16 ws).foldl compress H0
  hv.flatMap fun (x : UInt32) =>
    [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

/-- RIPEMD-160 of `m`. -/
def hash (m : ByteArray) : ByteArray :=
  ⟨(hashList m.toList).toArray⟩

end Spec

/-! ### Impl -/

namespace Impl

private def R : ByteArray :=
  ⟨(r.map Nat.toUInt8).toArray⟩

private def R' : ByteArray :=
  ⟨(r'.map Nat.toUInt8).toArray⟩

private def S : ByteArray :=
  ⟨(s.map Nat.toUInt8).toArray⟩

private def S' : ByteArray :=
  ⟨(s'.map Nat.toUInt8).toArray⟩

/-- The five chaining words. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32

/-- Steps `80 - n .. 79` of both lines. -/
private def steps (x : Array UInt32) (a b c d e a' b' c' d' e' : UInt32) : Nat → (State × State)
  | 0 => (⟨a, b, c, d, e⟩, ⟨a', b', c', d', e'⟩)
  | n + 1 =>
    let j := 79 - n
    let g := j / 16
    let t := rol (a + f g b c d + x[(R.get! j).toNat]! + k g) (S.get! j).toUInt32 + e
    let t' := rol (a' + f (4 - g) b' c' d' + x[(R'.get! j).toNat]! + k' g) (S'.get! j).toUInt32 + e'
    steps x e t b (rol c 10) d e' t' b' (rol c' 10) d' n

private def load (data : ByteArray) (off : Nat) : Nat → Array UInt32 → Array UInt32
  | 0, w => w
  | n + 1, w => load data (off + 4) n (w.push (le32 data off))

private def compress (h : State) (data : ByteArray) (off : Nat) : State :=
  let x := load data off 16 (Array.mkEmpty 16)
  let (l, r) := steps x h.a h.b h.c h.d h.e h.a h.b h.c h.d h.e 80
  ⟨h.b + l.c + r.d, h.c + l.d + r.e, h.d + l.e + r.a, h.e + l.a + r.b, h.a + l.b + r.c⟩

private def run (data : ByteArray) (off : Nat) (s : State) : Nat → State
  | 0 => s
  | n + 1 => run data (off + 64) (compress s data off) n

/-- RIPEMD-160 of `m`. -/
def hash (m : ByteArray) : ByteArray :=
  let full := m.size / 64
  let s := run m 0 ⟨0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0⟩ full
  let tail := (m.extract (64 * full) m.size).push 0x80 ++ zeros ((119 - m.size % 64) % 64)
  let tail := pushLe64 tail (8 * m.size).toUInt64
  let s := run tail 0 s (tail.size / 64)
  pushLe32 (pushLe32 (pushLe32 (pushLe32 (pushLe32 ByteArray.empty s.a) s.b) s.c) s.d) s.e

end Impl

end NearCrypto.Ripemd160

namespace NearCrypto

/-- RIPEMD-160 of `m`. -/
def ripemd160 (m : ByteArray) : ByteArray :=
  Ripemd160.Impl.hash m

end NearCrypto
