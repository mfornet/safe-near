import NearCrypto.Bytes
import NearCrypto.SpecConstants

/-!
# Keccak-256 and Keccak-512

The original Keccak submission as used by NEAR (`sha3::Keccak256`/`Keccak512`)
and Ethereum: the SHA-3 permutation with padding byte `0x01`, not SHA-3's
`0x06`. `Spec` is Keccak-f[1600] as FIPS 202 defines it (θ, ρ, π, χ, ι on 25
lanes, with the rotation offsets and round constants derived from their
definitions). `Impl` unrolls the round into 25 unboxed `UInt64` registers.
-/

namespace NearCrypto.Keccak

/-! ### Spec -/

namespace Spec

/-- Rotate left. -/
def rotl (x : UInt64) (n : Nat) : UInt64 :=
  if n % 64 = 0 then x else (x <<< n.toUInt64) ||| (x >>> (64 - n % 64).toUInt64)

/-- The state: lane `(x, y)` at index `x + 5 y`. -/
abbrev State :=
  Array UInt64

/-- The ρ offsets, from the triangular-number walk of FIPS 202 algorithm 2. -/
def rhoOffsets : List (Nat × Nat × Nat) :=
  ((List.range 24).foldl
      (fun (acc : List (Nat × Nat × Nat) × Nat × Nat) t =>
        let (l, x, y) := acc
        ((x, y, (t + 1) * (t + 2) / 2 % 64) :: l, y, (2 * x + 3 * y) % 5))
      ([], 1, 0)).1

/-- The offset of lane `(x, y)`. -/
def rho (x y : Nat) : Nat :=
  ((rhoOffsets.find? fun (a, b, _) => a == x && b == y).map fun (_, _, r) => r).getD 0

/-- One bit of the round-constant LFSR (FIPS 202 algorithm 5). -/
def rcBit (t : Nat) : Bool :=
  let r :=
    (List.range (t % 255)).foldl
      (fun (r : Nat) _ =>
        let r := r <<< 1;
        if r &&& 0x100 != 0 then r ^^^ 0x171 else r)
      1
  r &&& 1 == 1

/-- The round constant of round `i`. -/
def rc (i : Nat) : UInt64 :=
  (List.range 7).foldl
    (fun acc j =>
      if rcBit (j + 7 * i) then acc ||| ((1 : UInt64) <<< (2 ^ j - 1).toUInt64) else acc)
    0

/-- The 24 round constants. -/
def roundConstants : Array UInt64 :=
  (Array.range 24).map rc

/-- The ρ offsets by lane index. -/
def rhoTable : Array Nat :=
  Array.ofFn (n := 25) fun i => rho (i.val % 5) (i.val / 5)

/-- θ. -/
def theta (a : State) : State :=
  let c (x : Nat) := a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  Array.ofFn (n := 25) fun i =>
    let x := i.val % 5
    a[i.val]! ^^^ c ((x + 4) % 5) ^^^ rotl (c ((x + 1) % 5)) 1

/-- ρ and π: lane `(x, y)` rotated moves to `(y, 2x + 3y)`. -/
def rhoPi (a : State) : State :=
  Array.ofFn (n := 25) fun i =>
    let x' := i.val % 5
    let y' := i.val / 5
    -- the source `(x, y)` with `(y, 2x + 3y) = (x', y')`
    let y := x'
    let x := (List.range 5).find? (fun x => (2 * x + 3 * y) % 5 == y') |>.getD 0
    rotl a[x + 5 * y]! rhoTable[x + 5 * y]!

/-- χ. -/
def chi (b : State) : State :=
  Array.ofFn (n := 25) fun i =>
    let x := i.val % 5
    let y := i.val / 5
    b[i.val]! ^^^ (~~~b[(x + 1) % 5 + 5 * y]! &&& b[(x + 2) % 5 + 5 * y]!)

/-- One round. -/
def round (a : State) (i : Nat) : State :=
  let b := chi (rhoPi (theta a))
  b.set! 0 (b[0]! ^^^ roundConstants[i]!)

/-- Keccak-f[1600]. -/
def permute (a : State) : State :=
  (List.range 24).foldl round a

/-- Pad10*1 with the Keccak domain byte `0x01`, to a multiple of `rate` bytes. -/
def pad (rate : Nat) (m : List UInt8) : List UInt8 :=
  let q := rate - m.length % rate
  if q = 1 then m ++ [0x81] else m ++ [0x01] ++ List.replicate (q - 2) 0 ++ [0x80]

/-- XOR a block of `rate` bytes (little-endian lanes) into the state. -/
def absorb (a : State) (blk : List UInt8) : State :=
  Array.ofFn (n := 25) fun i =>
    let bytes := (blk.drop (8 * i.val)).take 8
    a[i.val]! ^^^ (bytes.zipIdx.foldl (fun acc (b, j) => acc ||| b.toUInt64 <<< (8 * j).toUInt64) 0)

/-- The first `n` bytes of the state, lane by lane little-endian. -/
def squeeze (a : State) (n : Nat) : List UInt8 :=
  (a.toList.flatMap fun (x : UInt64) =>
        (List.range 8).map fun j => (x >>> (8 * j).toUInt64).toUInt8).take
    n

/-- Keccak with `rate` bytes of rate and `n` bytes of output (`n ≤ rate`). -/
def sponge (rate n : Nat) (m : List UInt8) : List UInt8 :=
  let p := pad rate m
  let a :=
    (SpecConstants.chunks rate p).foldl (fun a blk => permute (absorb a blk)) (Array.replicate 25 0)
  squeeze a n

/-- Keccak-256. -/
def keccak256 (m : ByteArray) : ByteArray :=
  ⟨(sponge 136 32 m.toList).toArray⟩

/-- Keccak-512. -/
def keccak512 (m : ByteArray) : ByteArray :=
  ⟨(sponge 72 64 m.toList).toArray⟩

end Spec

/-! ### Impl -/

namespace Impl

/-- The 25 lanes; `a_i` is lane `(i % 5, i / 5)`. -/
structure State where
  a0 : UInt64
  a1 : UInt64
  a2 : UInt64
  a3 : UInt64
  a4 : UInt64
  a5 : UInt64
  a6 : UInt64
  a7 : UInt64
  a8 : UInt64
  a9 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64

private def RC : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

@[inline]
private def rotl (x : UInt64) (n : UInt64) : UInt64 :=
  (x <<< n) ||| (x >>> (64 - n))

/-- One round (θ, ρ, π, χ, ι) with round constant `rc`. -/
private def round (s : State) (rc : UInt64) : State :=
    let c0 := s.a0 ^^^ s.a5 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
    let c1 := s.a1 ^^^ s.a6 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
    let c2 := s.a2 ^^^ s.a7 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
    let c3 := s.a3 ^^^ s.a8 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
    let c4 := s.a4 ^^^ s.a9 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
    let d0 := c4 ^^^ rotl c1 1
    let d1 := c0 ^^^ rotl c2 1
    let d2 := c1 ^^^ rotl c3 1
    let d3 := c2 ^^^ rotl c4 1
    let d4 := c3 ^^^ rotl c0 1
    let b0 := (s.a0 ^^^ d0)
    let b1 := rotl (s.a6 ^^^ d1) 44
    let b2 := rotl (s.a12 ^^^ d2) 43
    let b3 := rotl (s.a18 ^^^ d3) 21
    let b4 := rotl (s.a24 ^^^ d4) 14
    let b5 := rotl (s.a3 ^^^ d3) 28
    let b6 := rotl (s.a9 ^^^ d4) 20
    let b7 := rotl (s.a10 ^^^ d0) 3
    let b8 := rotl (s.a16 ^^^ d1) 45
    let b9 := rotl (s.a22 ^^^ d2) 61
    let b10 := rotl (s.a1 ^^^ d1) 1
    let b11 := rotl (s.a7 ^^^ d2) 6
    let b12 := rotl (s.a13 ^^^ d3) 25
    let b13 := rotl (s.a19 ^^^ d4) 8
    let b14 := rotl (s.a20 ^^^ d0) 18
    let b15 := rotl (s.a4 ^^^ d4) 27
    let b16 := rotl (s.a5 ^^^ d0) 36
    let b17 := rotl (s.a11 ^^^ d1) 10
    let b18 := rotl (s.a17 ^^^ d2) 15
    let b19 := rotl (s.a23 ^^^ d3) 56
    let b20 := rotl (s.a2 ^^^ d2) 62
    let b21 := rotl (s.a8 ^^^ d3) 55
    let b22 := rotl (s.a14 ^^^ d4) 39
    let b23 := rotl (s.a15 ^^^ d0) 41
    let b24 := rotl (s.a21 ^^^ d1) 2
    ⟨(b0 ^^^ (~~~b1 &&& b2)) ^^^ rc, b1 ^^^ (~~~b2 &&& b3), b2 ^^^ (~~~b3 &&& b4),
    b3 ^^^ (~~~b4 &&& b0), b4 ^^^ (~~~b0 &&& b1), b5 ^^^ (~~~b6 &&& b7), b6 ^^^ (~~~b7 &&& b8),
    b7 ^^^ (~~~b8 &&& b9), b8 ^^^ (~~~b9 &&& b5), b9 ^^^ (~~~b5 &&& b6), b10 ^^^ (~~~b11 &&& b12),
    b11 ^^^ (~~~b12 &&& b13), b12 ^^^ (~~~b13 &&& b14), b13 ^^^ (~~~b14 &&& b10),
    b14 ^^^ (~~~b10 &&& b11), b15 ^^^ (~~~b16 &&& b17), b16 ^^^ (~~~b17 &&& b18),
    b17 ^^^ (~~~b18 &&& b19), b18 ^^^ (~~~b19 &&& b15), b19 ^^^ (~~~b15 &&& b16),
    b20 ^^^ (~~~b21 &&& b22), b21 ^^^ (~~~b22 &&& b23), b22 ^^^ (~~~b23 &&& b24),
    b23 ^^^ (~~~b24 &&& b20), b24 ^^^ (~~~b20 &&& b21)⟩

private def permute (s : State) : Nat → State
  | 0 => s
  | n + 1 => permute (round s RC[23 - n]!) n

/-- XOR the block at `off` (`lanes` lanes of it) into the state. -/
private def absorb (s : State) (data : ByteArray) (off lanes : Nat) : State :=
  let lane (i : Nat) : UInt64 := if i < lanes then le64 data (off + 8 * i) else 0
  ⟨s.a0 ^^^ lane 0, s.a1 ^^^ lane 1, s.a2 ^^^ lane 2, s.a3 ^^^ lane 3, s.a4 ^^^ lane 4,
    s.a5 ^^^ lane 5, s.a6 ^^^ lane 6, s.a7 ^^^ lane 7, s.a8 ^^^ lane 8, s.a9 ^^^ lane 9,
    s.a10 ^^^ lane 10, s.a11 ^^^ lane 11, s.a12 ^^^ lane 12, s.a13 ^^^ lane 13, s.a14 ^^^ lane 14,
    s.a15 ^^^ lane 15, s.a16 ^^^ lane 16, s.a17 ^^^ lane 17, s.a18 ^^^ lane 18, s.a19 ^^^ lane 19,
    s.a20 ^^^ lane 20, s.a21 ^^^ lane 21, s.a22 ^^^ lane 22, s.a23 ^^^ lane 23, s.a24 ^^^ lane 24⟩

private def run (rate : Nat) (data : ByteArray) (off : Nat) (s : State) : Nat → State
  | 0 => s
  | n + 1 => run rate data (off + rate) (permute (absorb s data off (rate / 8)) 24) n

/-- Keccak with `rate` bytes of rate and `n` bytes of output (`n ≤ 64`, `n ≤ rate`). -/
def sponge (rate n : Nat) (m : ByteArray) : ByteArray :=
  let full := m.size / rate
  let s :=
    run rate m 0 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ full
  let rest := m.size - rate * full
  let tail := m.extract (rate * full) m.size
  let tail :=
    if rest + 1 = rate then tail.push 0x81
    else (tail.push 0x01 ++ zeros (rate - rest - 2)).push 0x80
  let s := run rate tail 0 s 1
  let out :=
    pushLe64
      (pushLe64
        (pushLe64
          (pushLe64 (pushLe64 (pushLe64 (pushLe64 (pushLe64 ByteArray.empty s.a0) s.a1) s.a2) s.a3)
            s.a4)
          s.a5)
        s.a6)
      s.a7
  out.extract 0 n

/-- Keccak-256. -/
def keccak256 (m : ByteArray) : ByteArray :=
  sponge 136 32 m

/-- Keccak-512. -/
def keccak512 (m : ByteArray) : ByteArray :=
  sponge 72 64 m

end Impl

end NearCrypto.Keccak

namespace NearCrypto

/-- Keccak-256 (the original padding, as `sha3::Keccak256`). -/
def keccak256 (m : ByteArray) : ByteArray :=
  Keccak.Impl.keccak256 m

/-- Keccak-512 (the original padding, as `sha3::Keccak512`). -/
def keccak512 (m : ByteArray) : ByteArray :=
  Keccak.Impl.keccak512 m

end NearCrypto
