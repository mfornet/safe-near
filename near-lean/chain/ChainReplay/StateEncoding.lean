import ChainReplay.Wire
import NearRuntime.StateEncoding
import NearRuntime.TrieConstruction

/-! Encode the same typed ChainState and externally decoded catalogue as replay,
then independently construct its canonical trie. No native state bytes are read. -/
namespace ChainReplay.StateEncoding
open Lean

def execute (request : Json) : IO Json := do
  let (catalogues, initial) ← IO.ofExcept do
    object request ["formatVersion", "codes", "initialState"]
    let version : Nat ← field request "formatVersion"
    unless version == 1 do throw "unsupported formatVersion"
    pure (← field request "codes", ← field request "initialState")
  let codes ← loadCatalogue (catalogues : List Json)
  IO.ofExcept do
    let initial ← state codes initial
    let entries ← Near.StateEncoding.encode initial (codes.map fun code => (code.code.hash, code.bytes))
    let built ← Near.TrieConstruction.build entries
    let bytesJson (bytes : Near.Bytes) := toJson (bytes.map UInt8.toNat)
    let rows (entries : List (Near.Bytes × Near.Bytes)) :=
      toJson (entries.map fun (key, value) => toJson [bytesJson key, bytesJson value])
    return Json.mkObj [("initialEntries", rows entries), ("root", bytesJson built.root),
      ("witness", rows built.witness)]

end ChainReplay.StateEncoding

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let request ← IO.ofExcept (Lean.Json.parse input)
  IO.println (← ChainReplay.StateEncoding.execute request).compress
