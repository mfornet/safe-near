import ChainReplay.Wire
import NearRuntime.StateEncoding
import NearRuntime.TrieConstruction
import NearRuntime.QueueEncoding

/-! Encode the same typed ChainState and externally decoded catalogue as replay,
then independently construct its canonical trie. No native state bytes are read. -/
namespace ChainReplay.StateEncoding
open Lean

private def context (value : Json) : Result Near.QueueEncoding.Context := do
  object value ["receiptIds", "dataIds", "actionFormats", "delayed"]
  let rs : List (Nat × List Nat) ← field value "receiptIds"
  let rs ← rs.mapM fun (id, hash) => do pure (id, ← bytes hash)
  let ds : List Json ← field value "dataIds"
  let ds ← ds.mapM fun row => do
    object row ["id", "hash", "receiverId"]
    pure ({ id := ← field row "id", hash := ← byteField row "hash", receiver := ← field row "receiverId" } : Near.QueueEncoding.DataIdentity)
  let formats : List (Nat × String) ← field value "actionFormats"
  let formats ← formats.mapM fun (id, format) => do
    let format ← match format with
      | "legacy" => pure Near.ReceiptEncoding.ActionFormat.legacy
      | "v2" => pure Near.ReceiptEncoding.ActionFormat.v2
      | _ => throw "unsupported action format"
    pure (id, format)
  let delayed : Option Json ← field value "delayed"
  let delayed ← delayed.mapM fun row => do
    object row ["firstIndex", "forms"]
    let first ← u64 row "firstIndex"
    let forms : List Json ← field row "forms"
    let forms ← forms.mapM fun form => do
      let kind : String ← field form "kind"
      match kind with
      | "receipt" | "newStored" =>
        object form ["kind"]
        pure (if kind == "receipt" then Near.QueueEncoding.StorageForm.receipt else .newStored)
      | "storedV0" | "storedV1" =>
        object form ["kind", "gas", "size"]
        let gas ← u64 form "gas"
        let size ← u64 form "size"
        pure (if kind == "storedV0" then Near.QueueEncoding.StorageForm.storedV0 gas size else .storedV1 gas size)
      | _ => throw "unsupported delayed storage form"
    pure ({ firstIndex := first, forms } : Near.QueueEncoding.Delayed)
  pure { receipts := rs, data := ds, formats, delayed }

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
    let queue ← queue.mapM context
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
