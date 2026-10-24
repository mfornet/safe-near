/-!
# Width-`w` non-adjacent form

Shared by the scalar multiplications of edwards25519 and secp256k1. The recoding is the one of
`curve25519-dalek` (`non_adjacent_form`): windows of `w` bits read from 64-bit words.
-/

namespace NearCrypto.Wnaf

/-- The width-`w` non-adjacent form of `k < 2 ^ bits`: `bits + 1` digits, least significant
first, each zero or odd with absolute value below `2 ^ (w - 1)`. -/
def naf (bits w k : Nat) : Array Int :=
  let words : Array UInt64 := (Array.range (bits / 64 + 2)).map fun i => (k >>> (64 * i)).toUInt64
  let width : UInt64 := 1 <<< w.toUInt64
  let mask := width - 1
  let rec go : Nat → Nat → UInt64 → Array Int → Array Int
    | 0, _, _, digits => digits
    | fuel + 1, pos, carry, digits =>
      if pos > bits then digits
      else
        let idx := pos / 64
        let bit := (pos % 64).toUInt64
        let buf :=
          if pos % 64 < 64 - w then words[idx]! >>> bit
          else words[idx]! >>> bit ||| words[idx + 1]! <<< (64 - bit)
        let window := carry + (buf &&& mask)
        if window &&& 1 == 0 then go fuel (pos + 1) carry digits
        else
          if window < width / 2 then go fuel (pos + w) 0 (digits.set! pos (Int.ofNat window.toNat))
          else
            go fuel (pos + w) 1 (digits.set! pos (Int.ofNat window.toNat - Int.ofNat width.toNat))
  go (bits + 1) 0 0 (Array.replicate (bits + 1) 0)

end NearCrypto.Wnaf
