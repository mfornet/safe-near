import Lean

/-! Pure Keccak-256 and Keccak-512 (the Keccak submission's padding `0x01`,
as nearcore's `keccak256`/`keccak512` hosts use, not SHA-3's `0x06`), written
from the Keccak-f[1600] permutation of FIPS 202. Arithmetic uses wrapping
UInt64; this does not establish a refinement to the specification. -/
namespace Near.Keccak

private def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets of the ρ step, by lane `x + 5 * y`. -/
private def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

private def rotl (x n : UInt64) : UInt64 := if n == 0 then x else (x <<< n) ||| (x >>> (64 - n))

private def lane (a : Array UInt64) (x y : Nat) : UInt64 := a[x % 5 + 5 * (y % 5)]!

/-- One round: θ, ρ and π, χ, ι. -/
private def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let c := (List.range 5).toArray.map fun x =>
    lane a x 0 ^^^ lane a x 1 ^^^ lane a x 2 ^^^ lane a x 3 ^^^ lane a x 4
  let d := (List.range 5).toArray.map fun x => c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
  let a := (List.range 25).toArray.map fun i => a[i]! ^^^ d[i % 5]!
  -- B[y, 2x + 3y] = rot(A[x, y], r[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl (lane a x y) rotations[x + 5 * y]!)
  let a := (List.range 25).toArray.map fun i =>
    let (x, y) := (i % 5, i / 5)
    lane b x y ^^^ (~~~(lane b (x + 1) y) &&& lane b (x + 2) y)
  return a.set! 0 (a[0]! ^^^ rc)

def permute (a : Array UInt64) : Array UInt64 := roundConstants.foldl round a

/-- XOR one `rate`-byte block into the state, little-endian per lane. -/
private def absorbBlock (a : Array UInt64) (block : List UInt8) : Array UInt64 := Id.run do
  let mut a := a
  for i in [0:block.length / 8] do
    let mut word : UInt64 := 0
    for j in [0:8] do word := word ||| ((block[8 * i + j]!).toUInt64 <<< (8 * j).toUInt64)
    a := a.set! i (a[i]! ^^^ word)
  return a

/-- The `rate`-byte blocks of a padded message (its length is a multiple of `rate`). -/
private def blocks (rate : Nat) (bytes : List UInt8) : List (List UInt8) :=
  (List.range (bytes.length / rate)).map fun i => (bytes.drop (i * rate)).take rate

/-- The Keccak sponge with capacity `2 * outputBytes`; the output fits in one block. -/
def hash (outputBytes : Nat) (input : List UInt8) : List UInt8 :=
  let rate := 200 - 2 * outputBytes
  let padLength := rate - input.length % rate
  let padding := if padLength == 1 then [0x81] else [0x01] ++ List.replicate (padLength - 2) 0 ++ [0x80]
  let state := (blocks rate (input ++ padding)).foldl (fun a block => permute (absorbBlock a block))
    (Array.replicate 25 0)
  ((List.range outputBytes).map fun i => (state[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8)

def keccak256 (input : List UInt8) : List UInt8 := hash 32 input
def keccak512 (input : List UInt8) : List UInt8 := hash 64 input

end Near.Keccak
