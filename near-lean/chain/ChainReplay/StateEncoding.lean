import ChainReplay.QueueContext
import NearRuntime.StateEncoding
import NearRuntime.TrieConstruction
import NearRuntime.QueueEncoding

/-! Encode the same typed ChainState and externally decoded catalogue as replay,
then independently construct its canonical trie. No native state bytes are read. -/
namespace ChainReplay.StateEncoding
open Lean


def execute (request : Json) : IO Json := do
  let (catalogues, initial, queue, config) ← IO.ofExcept do
    object request ["formatVersion", "codes", "initialState", "queueContext", "runtimeConfig"]
    let version : Nat ← field request "formatVersion"
    unless version == 1 do throw "unsupported formatVersion"
    let queue : Option Json ← fromJson? ((request.getObjVal? "queueContext").toOption.getD .null)
    let config : Option Json ← fromJson? ((request.getObjVal? "runtimeConfig").toOption.getD .null)
    pure (← field request "codes", ← field request "initialState", queue, config)
  let codes ← loadCatalogue (catalogues : List Json)
  let cfg ← config.mapM fun row => do
    let (directory, protocol) ← IO.ofExcept do
      object row ["configDir", "protocolVersion"]
      let protocol : Nat ← field row "protocolVersion"
      unless 83 ≤ protocol && protocol ≤ 86 do throw "reference protocol range is 83–86"
      pure (← field row "configDir", protocol)
    Wasm.Near.RuntimeConfig.load directory protocol
  IO.ofExcept do
    let initial ← state codes initial
    let catalogue := codes.map fun code => (code.code.hash, code.bytes)
    let queue ← queue.mapM QueueContext.parse
    let entries ← match queue with
      | none => Near.StateEncoding.encode initial catalogue
      | some queue => Near.QueueEncoding.encode initial catalogue queue cfg
    let built ← Near.TrieConstruction.build entries
    let bytesJson (bytes : Near.Bytes) := toJson (bytes.map UInt8.toNat)
    let rows (entries : List (Near.Bytes × Near.Bytes)) :=
      toJson (entries.map fun (key, value) => toJson [bytesJson key, bytesJson value])
    let fields := [("initialEntries", rows entries), ("root", bytesJson built.root), ("witness", rows built.witness)]
    let extra ← match queue with
      | none => pure []
      | some queue => do pure [("queueEntries", rows (← Near.QueueEncoding.queues initial catalogue queue cfg))]
    return Json.mkObj (fields ++ extra)

end ChainReplay.StateEncoding

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let request ← IO.ofExcept (Lean.Json.parse input)
  IO.println (← ChainReplay.StateEncoding.execute request).compress
