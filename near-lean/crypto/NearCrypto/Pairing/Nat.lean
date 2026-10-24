import NearCrypto.Bytes
import NearCrypto.ModInv

/-!
# Integers modulo a prime, and their byte forms

The helpers of the pairing-friendly curves and P-256: modular exponentiation, inversion by Fermat's
little theorem, square roots for `p ≡ 3 (mod 4)` (every field here), and big- and little-endian
conversions of fixed-width integers.
-/

namespace NearCrypto.Pairing

/-- `a ^ e mod m`, square and multiply from the low bit. -/
def powMod (m a e : Nat) : Nat :=
  Id.run do
    let mut r := 1 % m
    let mut b := a % m
    for i in [0:e.log2 + 1] do
      if e.testBit i then
        r := r * b % m
      b := b * b % m
    return r

/-- The inverse of `a` modulo the prime `m`; zero for zero. The extended Euclidean algorithm
(`ModInv.invEuclid`: a few microseconds, against a quarter of a millisecond for the power at 381
bits), checked, with Fermat's little theorem as the fallback. -/
def invMod (m a : Nat) : Nat :=
  let a' := a % m
  if a' == 0 then 0
  else
    let r := ModInv.invEuclid a' m
    if r * a' % m == 1 then r else powMod m a (m - 2)

/-- A square root of `a` modulo the prime `m ≡ 3 (mod 4)`, when there is one. -/
def sqrtMod (m a : Nat) : Option Nat :=
  let y := powMod m a ((m + 1) / 4)
  if y * y % m == a % m then some y else none

/-- Whether `a` is a square modulo the prime `m` (zero is). -/
def isSquareMod (m a : Nat) : Bool :=
  a % m == 0 || powMod m a ((m - 1) / 2) == 1

/-- The value of `n` bytes of `b` from offset `off`, big-endian (in 64-bit words, so a few
operations on big numbers instead of one per byte). -/
def beNat (b : ByteArray) (off n : Nat) : Nat :=
  Id.run do
    let mut acc := 0
    let mut i := 0
    while i + 8 ≤ n do
      acc := acc <<< 64 ||| (be64 b (off + i)).toNat
      i := i + 8
    while i < n do
      acc := acc <<< 8 ||| (b.get! (off + i)).toNat
      i := i + 1
    return acc

/-- The value of `n` bytes of `b` from offset `off`, little-endian. -/
def leNat (b : ByteArray) (off n : Nat) : Nat :=
  Id.run do
    let mut acc := 0
    let mut i := 0
    while i + 8 ≤ n do
      acc := acc ||| (le64 b (off + i)).toNat <<< (8 * i)
      i := i + 8
    while i < n do
      acc := acc ||| (b.get! (off + i)).toNat <<< (8 * i)
      i := i + 1
    return acc

/-- The `n` big-endian bytes of `x` (`x < 256 ^ n`). -/
def toBe (x n : Nat) : ByteArray :=
  Id.run do
    let lead := n % 8
    let mut out := ByteArray.empty
    for i in [0:lead] do
      out := out.push (x >>> (8 * (n - 1 - i))).toUInt8
    for k in [0:n / 8] do
      out := pushBe64 out (x >>> (64 * (n / 8 - 1 - k))).toUInt64
    return out

/-- The `n` little-endian bytes of `x` (`x < 256 ^ n`). -/
def toLe (x n : Nat) : ByteArray :=
  Id.run do
    let mut out := ByteArray.empty
    for k in [0:n / 8] do
      out := pushLe64 out (x >>> (64 * k)).toUInt64
    for i in [0:n % 8] do
      out := out.push (x >>> (8 * (n / 8 * 8 + i))).toUInt8
    return out

end NearCrypto.Pairing
