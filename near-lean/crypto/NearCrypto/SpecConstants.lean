/-!
# Constants of the SHA-2 specifications

FIPS 180-4 defines the SHA-2 initial values and round constants as fractional
parts of square and cube roots of the first primes. The `Spec` of each hash
computes them from that definition; the `Impl` uses literal tables. The two
agree on every test vector.
-/

namespace NearCrypto.SpecConstants

/-- Whether `n` is prime (trial division). -/
def isPrime (n : Nat) : Bool :=
  2 ≤ n && (List.range n).all fun d => d < 2 || n % d != 0

/-- The first `n` primes (`n` at most 90). -/
def primes (n : Nat) : List Nat :=
  ((List.range 500).filter isPrime).take n

/-- The largest `r` with `r ^ k ≤ n` (for `n < 2 ^ 512`), found bit by bit. -/
def iroot (k n : Nat) : Nat :=
  (List.range 256).reverse.foldl (fun r b => if (r + 2 ^ b) ^ k ≤ n then r + 2 ^ b else r) 0

/-- `⌊frac(p ^ (1 / k)) · 2 ^ w⌋`: the `w` fractional bits of the `k`-th root of `p`. -/
def rootBits (k w p : Nat) : Nat :=
  iroot k (p * 2 ^ (k * w)) % 2 ^ w

/-- Consecutive blocks of `n` elements (the last may be shorter), consuming `fuel` blocks at most. -/
def chunksAux (n : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | fuel + 1, l => if l.isEmpty then [] else l.take n :: chunksAux n fuel (l.drop n)

/-- Consecutive blocks of `n` elements. -/
def chunks (n : Nat) (l : List α) : List (List α) :=
  chunksAux n l.length l

end NearCrypto.SpecConstants
