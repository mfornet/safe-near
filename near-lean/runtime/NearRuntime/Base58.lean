import NearRuntime.Types

/-! Base58 decoding of the code hash names the runtime keeps in `ContractCode.hash`.
A global contract is registered under the 32 raw hash bytes. -/
namespace Near.Base58

private def alphabet : List Char := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz".toList

private def digit? (c : Char) : Option Nat := alphabet.idxOf? c

/-- Big-endian bytes of a natural number. -/
private def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n => if n == 0 then [] else beBytes fuel (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Bitcoin-style base58: each leading `1` is a zero byte. -/
def decode (text : String) : Option Bytes := do
  let chars := text.toList
  let value ← chars.foldlM (fun acc c => (fun d => acc * 58 + d) <$> digit? c) 0
  let zeros := (chars.takeWhile (· == '1')).length
  return List.replicate zeros 0 ++ beBytes (chars.length * 2 + 2) value

end Near.Base58
