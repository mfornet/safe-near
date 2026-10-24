import ChainReplay.HostCrypto
import ChainReplay.Encode
import NearRuntime.TransactionRegistry

namespace ChainReplay.Transactions
open Lean Near

private def bytesJson (bytes : Near.Bytes) : Json := toJson (bytes.map UInt8.toNat)

def execute (request : Json) : IO Json := do
  let (catalogues, values, admission) ← IO.ofExcept do
    object request ["formatVersion", "codes", "transactions", "admission"]
    let version : Nat ← field request "formatVersion"
    unless version == 1 do throw "unsupported formatVersion"
    let admission : Option Json ← fromJson? ((request.getObjVal? "admission").toOption.getD .null)
    pure (← field request "codes", ← field request "transactions", admission)
  let codes ← loadCatalogue (catalogues : List Json)
  let inputs ← IO.ofExcept do
    (values : List Json).mapM fun row => do
      object row ["transaction", "blockHash"]
      pure ({ transaction := ← transaction codes (← field row "transaction"), blockHash := ← byteField row "blockHash" } : TransactionRegistry.Input)
  let catalogue := codes.map fun code => (code.code.hash, code.bytes)
  let bodies ← IO.ofExcept do
    inputs.mapM fun input => do
      let body ← TransactionEncoding.encode catalogue input.blockHash input.transaction
      pure (Json.mkObj [("body", bytesJson body), ("hash", bytesJson (Sha256.hash body)), ("bodySize", toJson body.length)])
  let registry ← admission.mapM fun admission => do
    let (directory, protocol, height, price, initial, bindings) ← IO.ofExcept do
      object admission ["configDir", "protocolVersion", "blockHeight", "gasPrice", "initialState", "receiptIds"]
      let protocol : Nat ← field admission "protocolVersion"
      unless 83 ≤ protocol && protocol ≤ 86 do throw "reference protocol range is 83–86"
      let initial ← state codes (← field admission "initialState")
      let ids : List (Nat × List Nat) ← field admission "receiptIds"
      let ids ← ids.mapM fun (id, hash) => do pure (id, ← bytes hash)
      pure (← field admission "configDir", protocol, ← u64 admission "blockHeight", ← amount admission "gasPrice", initial, ids)
    let cfg ← ChainReplay.HostCrypto.loadConfig directory protocol
    IO.ofExcept do
      let context : QueueEncoding.Context := { receipts := bindings, formats := bindings.map fun (id, _) => (id, .legacy) }
      -- This transport starts at a queue-free synthetic genesis. General typed
      -- contexts remain available to the library's observer.
      let _ ← StateEncoding.encode initial catalogue
      let result ← TransactionRegistry.observe cfg { blockHeight := height, gasPrice := price } catalogue initial inputs context
      pure (Json.mkObj [
        ("stateAfterTransactions", stateJson result.state),
        ("receiptIds", toJson (result.context.receipts.map fun (id, hash) => toJson [toJson id, bytesJson hash])),
        ("actionFormats", toJson (result.context.formats.map fun (id, _) => toJson [toJson id, toJson "legacy"])),
        ("attempts", toJson (result.attempts.map fun attempt => Json.mkObj [
          ("index", toJson attempt.index), ("receipt", (attempt.receipt.map receiptJson).getD .null),
          ("receiptHash", (attempt.receiptHash.map bytesJson).getD .null),
          ("error", (attempt.error.map (runtimeErrorJson inputs[attempt.index]!.transaction.signerId)).getD .null)]))])
  return Json.mkObj [("transactions", toJson bodies), ("registry", registry.getD .null)]

end ChainReplay.Transactions

def main : IO Unit := do
  let request ← IO.ofExcept (Lean.Json.parse (← (← IO.getStdin).readToEnd))
  IO.println (← ChainReplay.Transactions.execute request).compress
