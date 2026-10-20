import NearRuntime.TrieConstruction

open Lean Near.TrieAccounting

namespace TrieReplay

private def object (json : Json) (names : List String) : Except String Unit := do
  let fields ← json.getObj?
  for (name, _) in fields.toArray do
    unless names.contains name do throw s!"unknown field: {name}"

private def field (json : Json) (name : String) : Except String Json := json.getObjVal? name

private def bytes (json : Json) : Except String Bytes := do
  let values ← json.getArr?
  values.toList.mapM fun value => do
    let value ← value.getNat?
    if value ≥ 256 then throw "invalid byte"
    return UInt8.ofNat value

private def hash (json : Json) : Except String Hash := do
  let bytes ← bytes json
  if bytes.length != 32 then throw "invalid hash width"
  return bytes

private def bytesJson (value : Bytes) : Json := toJson (value.map UInt8.toNat)

private def referenceJson (value : ValueRef) : Json := Json.mkObj [
  ("hash", bytesJson value.hash), ("length", toJson value.length)]

private def resultJson (result : Result) : Json := Json.mkObj [
  ("reference", (result.reference.map referenceJson).getD .null),
  ("value", (result.value.map bytesJson).getD .null),
  ("counts", Json.mkObj [("disk", toJson result.state.disk), ("mem", toJson result.state.mem)]),
  ("events", toJson (result.state.events.map fun event => Json.mkObj [
    ("hash", bytesJson event.hash), ("kind", toJson event.kind), ("cached", toJson event.cached)]))]

private def runQueries (input : Json) (witness : Witness) (root : Hash) : Except String Json := do
  let mut state : Accounting := {}
  let mut results := []
  for row in (← (← field input "lookups").getArr?) do
    object row ["key", "accountNodes", "dereference", "resetCache"]
    let query : Query := {
      key := ← bytes (← field row "key")
      accountNodes := ← (← field row "accountNodes").getBool?
      dereference := ← (← field row "dereference").getBool?
      resetCache := ← (← field row "resetCache").getBool? }
    let result ← lookup witness root state query
    state := result.state
    results := results ++ [resultJson result]
  return Json.mkObj [("results", toJson results)]

private def witnessInput (input : Json) : Except String Json := do
  object input ["formatVersion", "root", "witness", "lookups"]
  unless (← (← field input "formatVersion").getNat?) == 1 do throw "unsupported trie formatVersion"
  let root ← hash (← field input "root")
  let rows ← (← field input "witness").getArr?
  let witness ← rows.toList.mapM fun row => do
    let pair ← row.getArr?
    unless pair.size == 2 do throw "invalid witness entry"
    return (← hash pair[0]!, ← bytes pair[1]!)
  let ids := witness.map Prod.fst
  unless ids.eraseDups.length == ids.length do throw "duplicate witness hash"
  for (id, payload) in witness do
    unless Near.Sha256.hash payload == id do throw "trie witness hash mismatch"
  runQueries input witness root

private def buildInput (input : Json) : Except String Json := do
  object input ["formatVersion", "entries", "lookups"]
  unless (← (← field input "formatVersion").getNat?) == 1 do throw "unsupported trie formatVersion"
  let rows ← (← field input "entries").getArr?
  let entries ← rows.toList.mapM fun row => do
    let pair ← row.getArr?
    unless pair.size == 2 do throw "invalid trie entry"
    return (← bytes pair[0]!, ← bytes pair[1]!)
  let built ← Near.TrieConstruction.build entries
  let result ← runQueries input built.witness built.root
  let fields ← result.getObj?
  return Json.mkObj (fields.toArray.toList ++ [
    ("root", bytesJson built.root),
    ("witness", toJson (built.witness.map fun (hash, value) => toJson [bytesJson hash, bytesJson value]))])

private def hashInput (input : Json) : Except String Json := do
  object input ["formatVersion", "hashInputs"]
  unless (← (← field input "formatVersion").getNat?) == 1 do throw "unsupported trie formatVersion"
  let values ← (← (← field input "hashInputs").getArr?).toList.mapM bytes
  return Json.mkObj [("hashes", toJson (values.map fun value => bytesJson (Near.Sha256.hash value)))]

def execute (input : Json) : Except String Json :=
  if (input.getObjVal? "hashInputs").isOk then hashInput input
  else if (input.getObjVal? "entries").isOk then buildInput input else witnessInput input

end TrieReplay

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let result ← IO.ofExcept (Json.parse input >>= TrieReplay.execute)
  IO.println result.compress
