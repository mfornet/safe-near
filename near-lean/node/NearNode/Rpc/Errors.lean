import Lean.Data.Json
import NearNode.Network.Keys
import NearNode.Rpc.Views

/-!
# Errors and request parameters

`RpcError` of `chain/jsonrpc-primitives/src/errors.rs`: the object of the `error` member of a JSON-RPC
response and the HTTP status that goes with it (`rpc_handler`). Requests that cannot be parsed are a
`REQUEST_VALIDATION_ERROR` with the `PARSE_ERROR` cause and status 400; a request the node understands but
cannot satisfy is a `HANDLER_ERROR` whose cause is the error of the method and whose `data` is the message
of the Rust error type; the status is 200 unless the handler timed out (408) or the block is below the
head (422).
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Network

structure RpcError where
  status : Nat
  error : Json

namespace RpcError

/-- `RpcError::parse_error`. -/
def parse (msg : String) : RpcError :=
  { status := 400,
    error :=
      Json.mkObj
        [("name", "REQUEST_VALIDATION_ERROR"),
          ("cause",
            Json.mkObj [("name", "PARSE_ERROR"), ("info", Json.mkObj [("error_message", msg)])]),
          ("code", Json.num (JsonNumber.fromInt (-32700))), ("message", "Parse error"),
          ("data", msg)] }

/-- `RpcError::method_not_found`. -/
def methodNotFound (method : String) : RpcError :=
  { status := 400,
    error :=
      Json.mkObj
        [("name", "REQUEST_VALIDATION_ERROR"),
          ("cause",
            Json.mkObj
              [("name", "METHOD_NOT_FOUND"), ("info", Json.mkObj [("method_name", method)])]),
          ("code", Json.num (JsonNumber.fromInt (-32601))), ("message", "Method not found"),
          ("data", method)] }

/-- A `HANDLER_ERROR` with the cause `name` (and its `info` when the error has fields). -/
def handler (name : String) (info : Option Json) (data : Json) (status : Nat := 200) : RpcError :=
  { status,
    error :=
      Json.mkObj
        [("name", "HANDLER_ERROR"),
          ("cause",
            Json.mkObj
              ([("name", Json.str name)] ++
                (match info with
                | some i => [("info", i)]
                | none => []))),
          ("code", Json.num (JsonNumber.fromInt (-32000))), ("message", "Server error"),
          ("data", data)] }

/-- `RpcError::new_internal_error`. -/
def internal (msg : String) : RpcError :=
  { status := 500,
    error :=
      Json.mkObj
        [("name", "INTERNAL_ERROR"),
          ("cause",
            Json.mkObj [("name", "INTERNAL_ERROR"), ("info", Json.mkObj [("error_message", msg)])]),
          ("code", Json.num (JsonNumber.fromInt (-32000))), ("message", "Server error"),
          ("data", msg)] }

end RpcError

abbrev R :=
  Except RpcError Json

/-! ### Parameters -/

def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => some v
  | .error _ => none

def hasField (j : Json) (k : String) : Bool :=
  (field? j k).isSome

/-- A hash from its base58 text (`CryptoHash` deserialization). -/
def parseHash (j : Json) : Except String CryptoHash :=
  match j with
  | .str s =>
    match base58Decode? s with
    | some b =>
      if b.size == 32 then pure ⟨b⟩
      else throw s!"invalid length {b.size}, expected base58-encoded 256-bit hash"
    | none => throw s!"invalid value: \"{s}\", expected base58-encoded 256-bit hash"
  | _ => throw "invalid type, expected a base58-encoded hash"

def parseAccount (j : Json) : Except String AccountId :=
  match j with
  | .str s =>
    if AccountId.isValid s then pure ⟨s⟩
    else throw s!"invalid value: \"{s}\", the Account ID is invalid"
  | _ => throw "invalid type: expected a string account id"

def parseU64 (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw "invalid type: expected an unsigned integer"

def parseKey (j : Json) : Except String PublicKey :=
  match j with
  | .str s =>
    match PublicKey.parse? s with
    | some k => pure k
    | none => throw s!"invalid value: \"{s}\", expected a public key"
  | _ => throw "invalid type: expected a public key string"

def failParse {α : Type} (msg : String) : Except RpcError α :=
  .error (RpcError.parse s!"Failed parsing args: {msg}")

/-- Lifts a parse failure to the `PARSE_ERROR` of a request. -/
def liftParse {α : Type} (r : Except String α) : Except RpcError α :=
  r.mapError fun m => RpcError.parse s!"Failed parsing args: {m}"

end Near.Node.Rpc
