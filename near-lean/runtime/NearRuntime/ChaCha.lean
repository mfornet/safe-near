import NearRuntime.Wire

/-! # `ChaCha20Rng` and slice shuffling

The generator `rand_chacha 0.3.1` seeds from 32 bytes (`ChaCha20Rng::from_seed`) and `rand 0.8.5`
draws bounded integers and shuffles slices with (`SliceRandom::shuffle`). The bandwidth scheduler
breaks ties between requests of equal allowance with it, seeded by the previous block hash.

The output stream is the ChaCha20 keystream of the seed with a 64-bit block counter starting at
zero and a zero stream: 32-bit word `k` is word `k % 16` of block `k / 16`. -/
namespace Near.ChaCha

private def mask : Nat := 2 ^ 32

private def rotl (x n : Nat) : Nat := (x * 2 ^ n % mask) ||| (x / 2 ^ (32 - n))

private def quarter (s : Array Nat) (a b c d : Nat) : Array Nat := Id.run do
  let mut s := s
  s := s.set! a ((s[a]! + s[b]!) % mask)
  s := s.set! d (rotl (s[d]! ^^^ s[a]!) 16)
  s := s.set! c ((s[c]! + s[d]!) % mask)
  s := s.set! b (rotl (s[b]! ^^^ s[c]!) 12)
  s := s.set! a ((s[a]! + s[b]!) % mask)
  s := s.set! d (rotl (s[d]! ^^^ s[a]!) 8)
  s := s.set! c ((s[c]! + s[d]!) % mask)
  s := s.set! b (rotl (s[b]! ^^^ s[c]!) 7)
  return s

private def doubleRound (s : Array Nat) : Array Nat :=
  let s := quarter s 0 4 8 12
  let s := quarter s 1 5 9 13
  let s := quarter s 2 6 10 14
  let s := quarter s 3 7 11 15
  let s := quarter s 0 5 10 15
  let s := quarter s 1 6 11 12
  let s := quarter s 2 7 8 13
  quarter s 3 4 9 14

/-- The 16 words of block `counter` of the keystream for `seed`. -/
def block (seed : Bytes) (counter : Nat) : Array Nat := Id.run do
  let key := (List.range 8).map fun i => Wire.number ((seed.drop (4 * i)).take 4)
  let initial : Array Nat :=
    #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ key.toArray ++
      #[counter % mask, counter / mask % mask, 0, 0]
  let mut state := initial
  for _ in List.range 10 do
    state := doubleRound state
  return (state.zip initial).map fun (a, b) => (a + b) % mask

/-- The generator: its seed and how many 32-bit words it has produced. -/
structure Rng where
  seed : Bytes
  used : Nat := 0

def Rng.ofSeed (seed : Bytes) : Rng := { seed }

/-- `RngCore::next_u32`. -/
def Rng.nextU32 (rng : Rng) : Nat × Rng :=
  ((block rng.seed (rng.used / 16))[rng.used % 16]!, { rng with used := rng.used + 1 })

/-- Rejection sampling of `UniformInt::sample_single_inclusive`: accept the high word of
`v * range` when its low word is within the zone. -/
private partial def draw (range zone : Nat) (rng : Rng) : Nat × Rng :=
  let (v, rng) := rng.nextU32
  let product := v * range
  if product % mask ≤ zone then (product / mask, rng) else draw range zone rng

/-- `rng.gen_range(0..bound)` for a `u32` bound with `rand 0.8.5`'s widening multiply. -/
def Rng.below (rng : Rng) (bound : Nat) : Nat × Rng :=
  if bound % mask == 0 then rng.nextU32 else
  draw bound (bound * 2 ^ (32 - (Nat.log2 bound + 1)) - 1) rng

/-- `SliceRandom::shuffle`: Fisher–Yates from the back with `gen_index`. -/
def Rng.shuffle [Inhabited α] (rng : Rng) (items : Array α) : Array α × Rng := Id.run do
  let mut items := items
  let mut rng := rng
  for k in List.range (items.size - 1) do
    let i := items.size - 1 - k
    let (j, rng') := rng.below (i + 1)
    rng := rng'
    let a := items[i]!
    items := items.set! i items[j]!
    items := items.set! j a
  return (items, rng)

end Near.ChaCha
