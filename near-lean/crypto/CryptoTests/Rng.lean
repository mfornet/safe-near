/-!
# A seeded pseudo-random stream

SplitMix64, as a pure state, so a failing differential test reproduces from its seed.
-/

/-- SplitMix64. -/
structure Rng where
  state : UInt64

namespace Rng

def next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- `n` random bytes. -/
def bytes (r : Rng) (n : Nat) : ByteArray × Rng :=
  Id.run do
    let mut out := ByteArray.empty
    let mut r := r
    for _ in [0:n] do
      let (x, r') := r.next
      out := out.push x.toUInt8
      r := r'
    return (out, r)

/-- A random number below `n`. -/
def below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (x.toNat % n, r)

end Rng
