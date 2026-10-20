import ChainReplay.Wire
import NearRuntime.ReceiptEncoding

/-! Typed receipt encoding and independently derived native identity graphs.
The only graph roots are original byte messages or explicit initial hash inputs;
all derived nodes can refer only to earlier graph nodes. -/
namespace ChainReplay.ReceiptEncoding
open Lean

private def byteArray (input : Json) : Result Near.Bytes := do
  bytes (← fromJson? input)

private def graph (operations : List Json) : Result (List Near.NativeIdentity.Hash) := do
  let mut hashes := #[]
  for operation in operations do
    let kind : String ← field operation "kind"
    let value ← match kind with
      | "input" => do
        object operation ["kind", "hash"]
        Near.NativeIdentity.checkedHash (← byteArray (← field operation "hash"))
      | "hash" => do
        object operation ["kind", "bytes"]
        pure (Near.Sha256.hash (← byteArray (← field operation "bytes")))
      | "transaction" | "receipt" | "action" | "data" | "randomSeed" => do
        object operation (if kind == "transaction" then ["kind", "base", "blockHeight"]
          else if kind == "randomSeed" then ["kind", "base", "seed"]
          else ["kind", "base", "blockHeight", "index"])
        let index : Nat ← field operation "base"
        let some base := hashes[index]? | throw "identity base is unavailable"
        if kind == "randomSeed" then
          Near.NativeIdentity.randomSeed base (← byteArray (← field operation "seed"))
        else
          let height ← u64 operation "blockHeight"
          if kind == "transaction" then Near.NativeIdentity.transactionReceipt base height
          else
            let index ← u64 operation "index"
            if kind == "receipt" then Near.NativeIdentity.receipt base height index
            else if kind == "action" then Near.NativeIdentity.action base height index
            else Near.NativeIdentity.data base height index
      | _ => throw "unknown identity operation"
    hashes := hashes.push value
  return hashes.toList

private def bindings (hashes : List Near.NativeIdentity.Hash) (values : List (Nat × Nat)) :
    Result Near.NativeIdentity.Bindings := do
  values.mapM fun (id, position) => do
    let some hash := hashes[position]? | throw "identity binding is unavailable"
    pure (id, hash)

def execute (request : Json) : IO Json := do
  let (catalogues, operations, rs, ds, values, formats, received) ← IO.ofExcept do
    object request ["formatVersion", "codes", "identities", "receiptIds", "dataIds", "receipts", "actionFormats", "receivedData"]
    let version : Nat ← field request "formatVersion"
    unless version == 1 do throw "unsupported formatVersion"
    pure (← field request "codes", ← field request "identities", ← field request "receiptIds",
      ← field request "dataIds", ← field request "receipts", ← field request "actionFormats", ← field request "receivedData")
  let codes ← loadCatalogue (catalogues : List Json)
  IO.ofExcept do
    let hashes ← graph operations
    let rs ← bindings hashes rs
    let ds ← bindings hashes ds
    Near.NativeIdentity.validate rs
    Near.NativeIdentity.validate ds
    let values ← (values : List Json).mapM (receipt codes)
    unless values.length == (formats : List String).length do throw "receipt format count mismatch"
    let formats ← formats.mapM fun format => match format with
      | "legacy" => pure Near.ReceiptEncoding.ActionFormat.legacy
      | "v2" => pure Near.ReceiptEncoding.ActionFormat.v2
      | _ => throw "unsupported action format"
    let encoded ← (formats.zip values).mapM fun (format, value) =>
      Near.ReceiptEncoding.encode rs ds (codes.map fun code => (code.code.hash, code.bytes)) format value
    let received ← (received : List (Option (List Nat))).mapM fun value => do
      Near.ReceiptEncoding.receivedData (← value.mapM bytes)
    let rows (values : List Near.Bytes) := toJson (values.map fun bytes => toJson (bytes.map UInt8.toNat))
    return Json.mkObj [("hashes", rows hashes), ("receipts", rows encoded), ("receivedData", rows received)]

end ChainReplay.ReceiptEncoding

def main : IO Unit := do
  let request ← IO.ofExcept (Lean.Json.parse (← (← IO.getStdin).readToEnd))
  IO.println (← ChainReplay.ReceiptEncoding.execute request).compress
