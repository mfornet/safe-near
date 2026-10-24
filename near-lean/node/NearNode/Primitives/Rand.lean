import NearNode.Primitives.Basic

/-!
# Seeded randomness

The `rand_chacha` 0.3 `ChaCha20Rng` and the `rand` 0.8 functions that nearcore uses with it to pick
chunk validators: `gen_range` on `u32` (widening multiply with rejection) and the Fisher-Yates
`shuffle`. The output is consensus-critical, so each step follows the crates.
-/

namespace Near.Node

/-- `ChaCha20Rng`: 64-bit block counter, zero stream, and the words of the current block. -/
structure ChaCha20Rng where
  key : Array UInt32
  counter : UInt64
  block : Array UInt32
  next : Nat
  deriving Inhabited

namespace ChaCha20Rng

private def rotl (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

private def quarterRound (s : Array UInt32) (a b c d : Nat) : Array UInt32 :=
  let s := s.set! a (s[a]! + s[b]!)
  let s := s.set! d (rotl (s[d]! ^^^ s[a]!) 16)
  let s := s.set! c (s[c]! + s[d]!)
  let s := s.set! b (rotl (s[b]! ^^^ s[c]!) 12)
  let s := s.set! a (s[a]! + s[b]!)
  let s := s.set! d (rotl (s[d]! ^^^ s[a]!) 8)
  let s := s.set! c (s[c]! + s[d]!)
  s.set! b (rotl (s[b]! ^^^ s[c]!) 7)

private def doubleRound (s : Array UInt32) : Array UInt32 :=
  let s := quarterRound s 0 4 8 12
  let s := quarterRound s 1 5 9 13
  let s := quarterRound s 2 6 10 14
  let s := quarterRound s 3 7 11 15
  let s := quarterRound s 0 5 10 15
  let s := quarterRound s 1 6 11 12
  let s := quarterRound s 2 7 8 13
  quarterRound s 3 4 9 14

/-- The 16 words of the block at `counter` (20 rounds). -/
def chachaBlock (key : Array UInt32) (counter : UInt64) : Array UInt32 :=
  let constants : Array UInt32 := #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]
  let init : Array UInt32 :=
    constants ++ key ++ #[counter.toUInt32, (counter >>> 32).toUInt32, 0, 0]
  let final := (List.range 10).foldl (fun s _ => doubleRound s) init
  (final.zip init).map fun (a, b) => a + b

/-- `SeedableRng::from_seed` with a 32-byte seed. -/
def fromSeed (seed : ByteArray) : ChaCha20Rng :=
  let word (i : Nat) : UInt32 :=
    (seed.get! (4 * i)).toUInt32 ||| (seed.get! (4 * i + 1)).toUInt32 <<< 8 |||
      (seed.get! (4 * i + 2)).toUInt32 <<< 16 |||
      (seed.get! (4 * i + 3)).toUInt32 <<< 24
  { key := (Array.range 8).map word, counter := 0, block := #[], next := 16 }

/-- `next_u32`: the words of consecutive blocks in order. -/
def nextU32 (r : ChaCha20Rng) : UInt32 × ChaCha20Rng :=
  if r.next < 16 then (r.block[r.next]!, { r with next := r.next + 1 })
  else
    let block := chachaBlock r.key r.counter
    (block[0]!,
      { r with
        counter := r.counter + 1, block, next := 1 })

/-- `next_u64`: two consecutive words, the first the low half. -/
def nextU64 (r : ChaCha20Rng) : UInt64 × ChaCha20Rng :=
  let (lo, r) := r.nextU32
  let (hi, r) := r.nextU32
  (hi.toUInt64 <<< 32 ||| lo.toUInt64, r)

/-- `gen_range(0..n)` on `u32`: `sample_single_inclusive` with the zone approximation, resampling
while the low half of `v * n` is above it. `n` must be positive. -/
def genRange (r : ChaCha20Rng) (n : UInt32) : UInt32 × ChaCha20Rng :=
  let zone := (n <<< (31 - n.toNat.log2).toUInt32) - 1
  let rec go : Nat → ChaCha20Rng → UInt32 × ChaCha20Rng
    | 0, r => (0, r)
    | fuel + 1, r =>
      let (v, r) := r.nextU32
      let m := v.toUInt64 * n.toUInt64
      if (m &&& 0xFFFFFFFF).toUInt32 ≤ zone then ((m >>> 32).toUInt32, r) else go fuel r
  go 4096 r

/-- `SliceRandom::shuffle`: swap each position from the end with a uniform earlier or equal one. -/
def shuffle (r : ChaCha20Rng) (a : Array α) : Array α × ChaCha20Rng :=
  Id.run do
    let mut a := a
    let mut r := r
    for k in [1:a.size] do
      let i := a.size - k
      let (j, r') := r.genRange (i + 1).toUInt32
      r := r'
      a := a.swapIfInBounds i j.toNat
    return (a, r)

end ChaCha20Rng

end Near.Node
