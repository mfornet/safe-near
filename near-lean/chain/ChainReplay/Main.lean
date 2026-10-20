import ChainReplay.Encode

namespace ChainReplay

open Lean Wasm.Near Near

/-- Exactly the requested block sequence, including idle blocks. Rejected
attempts are recorded; later blocks remain explicitly unrun. -/
def run (protocol : Nat) (cfg : RuntimeConfig) (codes : Catalogue) (initial : Snapshot) (blocks : List Block) : Json :=
  let rec go (s : Snapshot) (trace : List Json) : List Block → Json
    | [] => finish s trace "blocksExhausted" 0
    | block :: rest =>
      match step cfg (codeOf codes) s block with
      | .error (.unavailableIndex position) =>
        let rejected := obj (snapshotFields s ++ [("scheduleError", obj [
          kind "unavailableIndex", ("position", toJson position)])])
        finish s (trace ++ [rejected]) "invalidSchedule" rest.length
      | .ok (next, result) =>
        let trace := trace ++ [applyJson cfg block.txs next result]
        if result.issue.isSome then finish next trace "executionIssue" rest.length
        else go next trace rest
  go initial [] blocks
where
  finish (s : Snapshot) (trace : List Json) (stop : String) (unrun : Nat) : Json := obj [
    ("formatVersion", toJson (1 : Nat)), ("protocolVersion", toJson protocol),
    ("model", toJson "near-lean-chain"),
    ("initialState", stateJson initial.state),
    ("initialPendingReceipts", toJson (initial.pending.map receiptJson)),
    ("blocks", toJson trace), ("stop", toJson stop), ("unrunBlocks", toJson unrun),
    ("quiescent", toJson s.quiescent),
    ("codeCatalogue", toJson (codes.map fun entry => obj [
      ("hash", toJson entry.code.hash), ("size", toJson entry.code.size)]))]

def execute (request : Json) : IO Json := do
  let (protocol, configDir, catalogues, initial, pending, blocks) ←
    IO.ofExcept do
        object request
            ["formatVersion", "protocolVersion", "configDir", "codes", "initialState",
              "pendingReceipts", "blocks"]
        let version : Nat ← field request "formatVersion"
        unless version == 1 do
          throw "unsupported formatVersion"
        let protocol : Nat ← field request "protocolVersion"
        unless 83 ≤ protocol && protocol ≤ 86 do
          throw "reference protocol range is 83–86"
        pure
            (protocol, ← field request "configDir", ← field request "codes",
              ← field request "initialState", ← field request "pendingReceipts",
              ← field request "blocks")
  let codes ← loadCatalogue (catalogues : List Json)
  let snapshot : Snapshot ←
    IO.ofExcept do
        pure
            { state := ← state codes initial,
              pending := ← (pending : List Json).mapM (receipt codes) }
  let blocks ← IO.ofExcept ((blocks : List Json).mapM (block codes))
  let cfg ← RuntimeConfig.load (configDir : String) protocol
  pure (run protocol cfg codes snapshot blocks)

end ChainReplay

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let json ← IO.ofExcept (Lean.Json.parse input)
  let output ← ChainReplay.execute json
  (← IO.getStdout).putStrLn output.compress
