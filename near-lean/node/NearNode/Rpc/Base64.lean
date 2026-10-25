/-!
# Base64

The standard alphabet with padding (`base64::STANDARD`), as `serde_with::base64::Base64` writes the
bytes of `FunctionArgs`, `StoreKey`, `StoreValue` and contract code, and as the transaction of
`send_tx` arrives.
-/

namespace Near.Node.Rpc

private def alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- Base64 text of bytes, padded. -/
def base64Encode (b : ByteArray) : String :=
  Id.run do
    let mut out := ""
    let n := b.size
    let mut i := 0
    while i + 3 ≤ n do
      let x := (b[i]!.toNat <<< 16) ||| (b[i + 1]!.toNat <<< 8) ||| b[i + 2]!.toNat
      out :=
        out.push alphabet[x >>> 18]! |>.push alphabet[(x >>> 12) &&& 63]! |>.push
            alphabet[(x >>> 6) &&& 63]! |>.push
          alphabet[x &&& 63]!
      i := i + 3
    if n - i == 1 then
      let x := b[i]!.toNat <<< 16
      out :=
        out.push alphabet[x >>> 18]! |>.push alphabet[(x >>> 12) &&& 63]! |>.push '=' |>.push '='
    else if n - i == 2 then
      let x := (b[i]!.toNat <<< 16) ||| (b[i + 1]!.toNat <<< 8)
      out :=
        out.push alphabet[x >>> 18]! |>.push alphabet[(x >>> 12) &&& 63]! |>.push
            alphabet[(x >>> 6) &&& 63]! |>.push
          '='
    return out

private def value? (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 65)
  else
    if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 97 + 26)
    else
      if '0' ≤ c && c ≤ '9' then some (c.toNat - 48 + 52)
      else if c == '+' then some 62 else if c == '/' then some 63 else none

/-- Decodes padded standard base64; `none` for anything else (the `base64` crate's strict decoder:
the length is a multiple of four, padding only at the end, and the unused bits are zero). -/
def base64Decode? (s : String) : Option ByteArray := do
  let cs := s.toList.toArray
  if cs.size % 4 != 0 then
    none
  let mut out := ByteArray.empty
  let groups := cs.size / 4
  for g in [0:groups] do
    let c0 := cs[4 * g]!
    let c1 := cs[4 * g + 1]!
    let c2 := cs[4 * g + 2]!
    let c3 := cs[4 * g + 3]!
    let last := g + 1 == groups
    let v0 ← value? c0
    let v1 ← value? c1
    if last && c2 == '=' then
      if c3 != '=' then
        none
      if v1 &&& 15 != 0 then
        none
      out := out.push ((v0 <<< 2 ||| v1 >>> 4).toUInt8)
    else
      let v2 ← value? c2
      if last && c3 == '=' then
        if v2 &&& 3 != 0 then
          none
        out :=
          out.push ((v0 <<< 2 ||| v1 >>> 4).toUInt8) |>.push
            (((v1 &&& 15) <<< 4 ||| v2 >>> 2).toUInt8)
      else
        let v3 ← value? c3
        out :=
          out.push ((v0 <<< 2 ||| v1 >>> 4).toUInt8) |>.push
              (((v1 &&& 15) <<< 4 ||| v2 >>> 2).toUInt8) |>.push
            (((v2 &&& 3) <<< 6 ||| v3).toUInt8)
  pure out

end Near.Node.Rpc
