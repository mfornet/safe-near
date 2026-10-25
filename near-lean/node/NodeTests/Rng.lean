/-!
# A seeded generator for the tests
-/

/-- SplitMix64. -/
structure Rng where
  s : UInt64

namespace Rng

def next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

def below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (x.toNat % n, r)

end Rng

abbrev R :=
  StateM Rng

def below (n : Nat) : R Nat :=
  modifyGet (·.below n)
