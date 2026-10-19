import NearVM.State

namespace Wasm.Near

/-- V2 account syntax: lowercase ASCII letters/digits separated by single
`-`, `_`, or `.` characters, with alphanumeric endpoints. -/
def accountIdFormat : Bool → List UInt8 → Bool
  | previousSeparator, [] => !previousSeparator
  | previousSeparator, byte :: rest =>
    let n := byte.toNat
    if (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) then accountIdFormat false rest
    else if (n == 45 || n == 95 || n == 46) && !previousSeparator then accountIdFormat true rest
    else false

def validAccountIdBytes (bytes : List UInt8) : Bool :=
  2 ≤ bytes.length && bytes.length ≤ 64 && accountIdFormat true bytes

end Wasm.Near
