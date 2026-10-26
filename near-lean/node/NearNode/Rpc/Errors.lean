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

/-- Rust's `{:?}` of a character. -/
private def charDebug (c : Char) : String :=
  match c with
  | '\n' => "'\\n'"
  | '\t' => "'\\t'"
  | '\r' => "'\\r'"
  | '\'' => "'\\''"
  | '\\' => "'\\\\'"
  | _ => s!"'{c}'"

/-- Rust's `{:?}` of a string. -/
def stringDebug (s : String) : String :=
  "\"" ++
    String.join
      (s.toList.map fun c =>
        match c with
        | '"' => "\\\""
        | '\\' => "\\\\"
        | '\n' => "\\n"
        | '\t' => "\\t"
        | '\r' => "\\r"
        | _ => c.toString) ++
    "\""

/-- Why `near_account_id::validate` refuses `s` (the `Display` of `ParseAccountError`). -/
def accountIdError (s : String) : Option String :=
  Id.run do
    let n := s.length
    if n < 2 then
      return some "the Account ID is too short"
    if n > 64 then
      return some "the Account ID is too long"
    let mut lastSeparator := true
    let mut last : Option (Nat × Char) := none
    let mut i := 0
    for c in s.toList do
      last := some (i, c)
      let isChar := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
      let isSep := c == '-' || c == '_' || c == '.'
      if !isChar && !isSep then
        return some s!"the Account ID contains an invalid character {charDebug c} at index {i}"
      let separator := isSep
      if separator && lastSeparator then
        return some s!"the Account ID has a redundant separator {charDebug c} at index {i}"
      lastSeparator := separator
      i := i + 1
    if lastSeparator then
      match last with
      | some (j, c) =>
        return some s!"the Account ID has a redundant separator {charDebug c} at index {j}"
      | none =>
        pure ()
    return none

def parseAccount (j : Json) : Except String AccountId :=
  match j with
  | .str s =>
    match accountIdError s with
    | none => pure ⟨s⟩
    | some why => throw s!"invalid value: {stringDebug s}, {why}"
  | _ => throw "invalid type: expected a string account id"

def parseU64 (j : Json) : Except String Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throw "invalid type: expected an unsigned integer"

/-- serde's words for a JSON value found where another type was expected (`Unexpected`). -/
def serdeFound : Json → String
  | .null => "null"
  | .bool b => s!"boolean `{b}`"
  | .num n => s!"integer `{n}`"
  | .str s => s!"string {stringDebug s}"
  | .arr _ => "sequence"
  | .obj _ => "map"

/-- A public key from its text (`PublicKey::from_str`): `ed25519:` and `secp256k1:` followed by the base58 of the key, a text with no
prefix being an Ed25519 key. -/
def parseKey (j : Json) : Except String PublicKey :=
  match j with
  | .str s =>
    let (kind, body) :=
      match s.splitOn ":" with
      | [] | [_] => ("ed25519", s)
      | k :: rest => (k, ":".intercalate rest)
    let decode (size : Nat) (mk : ByteArray → PublicKey) : Except String PublicKey :=
      match base58Decode? body with
      | none => throw s!"invalid value: {stringDebug s}, expected a public key"
      | some b =>
        if b.size == size then pure (mk b)
        else throw s!"invalid key length: expected the input of {size} bytes, but {b.size} was given"
    match kind with
    | "ed25519" => decode 32 .ed25519
    | "secp256k1" => decode 64 .secp256k1
    | other => throw s!"unknown key type '{other}'"
  | _ => throw s!"invalid type: {serdeFound j}, expected a string"

def failParse {α : Type} (msg : String) : Except RpcError α :=
  .error (RpcError.parse s!"Failed parsing args: {msg}")

/-- Lifts a parse failure to the `PARSE_ERROR` of a request. -/
def liftParse {α : Type} (r : Except String α) : Except RpcError α :=
  r.mapError fun m => RpcError.parse s!"Failed parsing args: {m}"

end Near.Node.Rpc
