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

/-- The inverse of `a` modulo the prime `m`; zero for zero. Below `2²⁵⁶` by `ModInv` (checked
there), above by Fermat's little theorem. -/
def invMod (m a : Nat) : Nat :=
  if m < 2 ^ 256 then ModInv.inv a m else powMod m a (m - 2)

/-- A square root of `a` modulo the prime `m ≡ 3 (mod 4)`, when there is one. -/
def sqrtMod (m a : Nat) : Option Nat :=
  let y := powMod m a ((m + 1) / 4)
  if y * y % m == a % m then some y else none

/-- Whether `a` is a square modulo the prime `m` (zero is). -/
def isSquareMod (m a : Nat) : Bool :=
  a % m == 0 || powMod m a ((m - 1) / 2) == 1

/-- The value of `n` bytes of `b` from offset `off`, big-endian. -/
def beNat (b : ByteArray) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc <<< 8 ||| (b.get! (off + i)).toNat) 0

/-- The value of `n` bytes of `b` from offset `off`, little-endian. -/
def leNat (b : ByteArray) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc ||| (b.get! (off + i)).toNat <<< (8 * i)) 0

/-- The `n` big-endian bytes of `x` (`x < 256 ^ n`). -/
def toBe (x n : Nat) : ByteArray :=
  ByteArray.mk <| ((List.range n).map fun i => (x >>> (8 * (n - 1 - i))).toUInt8).toArray

/-- The `n` little-endian bytes of `x` (`x < 256 ^ n`). -/
def toLe (x n : Nat) : ByteArray :=
  ByteArray.mk <| ((List.range n).map fun i => (x >>> (8 * i)).toUInt8).toArray

end NearCrypto.Pairing
