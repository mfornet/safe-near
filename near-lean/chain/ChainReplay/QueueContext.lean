import ChainReplay.Wire
import NearRuntime.QueueEncoding

namespace ChainReplay.QueueContext
open Lean

def parse (value : Json) : Result Near.QueueEncoding.Context := do
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

end ChainReplay.QueueContext
