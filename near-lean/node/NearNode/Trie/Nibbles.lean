import NearNode.Primitives.Basic

/-!
# Nibble paths

A path is a `ByteArray` with one nibble (0 to 15) per byte. A node stores its path in hex-prefix
form: a flag byte (`0x20` for a leaf, `0x10` when the length is odd, with the first nibble in the
low half) followed by the remaining nibbles packed in pairs (`NibbleSlice::encoded`).
-/

namespace Near.Node.Trie

/-- A nibble path, one nibble per byte. -/
abbrev Nibs :=
  ByteArray

/-- The nibbles of a key. -/
def toNibs (key : ByteArray) : Nibs :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (2 * key.size)
    for b in key do
      out := (out.push (b >>> 4)).push (b &&& 15)
    return out

/-- The key of an even-length path. -/
def ofNibs (n : Nibs) : ByteArray :=
  Id.run do
    let mut out := ByteArray.emptyWithCapacity (n.size / 2)
    for i in [0:n.size / 2] do
      out := out.push ((n.get! (2 * i) <<< 4) ||| n.get! (2 * i + 1))
    return out

/-- How many nibbles `a[i..]` and `b` share at the start. -/
def common (a : Nibs) (i : Nat) (b : Nibs) : Nat :=
  let limit := min (a.size - i) b.size
  let rec go (j : Nat) : Nat → Nat
    | 0 => j
    | fuel + 1 => if j < limit && a.get! (i + j) == b.get! j then go (j + 1) fuel else j
  go 0 limit

/-- `a[i..j]`. -/
def slice (a : Nibs) (i j : Nat) : Nibs :=
  a.extract i j

/-- The hex-prefix form of a path (`NibbleSlice::encoded`). -/
def hpEncode (leaf : Bool) (n : Nibs) : ByteArray :=
  Id.run do
    let odd := n.size % 2 == 1
    let flag : UInt8 := (if leaf then 0x20 else 0) ||| (if odd then 0x10 ||| n.get! 0 else 0)
    let mut out := (ByteArray.emptyWithCapacity (n.size / 2 + 1)).push flag
    let mut i := n.size % 2
    while i < n.size do
      out := out.push ((n.get! i <<< 4) ||| n.get! (i + 1))
      i := i + 2
    return out

/-- Size of `hpEncode n`. -/
def hpSize (nibbles : Nat) : Nat :=
  nibbles / 2 + 1

/-- The path of a hex-prefix form and its leaf flag (`NibbleSlice::from_encoded`), which looks only
at the two flag bits. -/
def hpDecode (b : ByteArray) : Except String (Nibs × Bool) := do
  if b.size == 0 then
    throw "empty compact trie path"
  let first := b.get! 0
  let mut out := ByteArray.emptyWithCapacity (2 * b.size)
  if first &&& 0x10 != 0 then
    out := out.push (first &&& 15)
  for i in [1:b.size] do
    let x := b.get! i
    out := (out.push (x >>> 4)).push (x &&& 15)
  return (out, first &&& 0x20 != 0)

end Near.Node.Trie
