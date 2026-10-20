import NearRuntime.Nonce

open Lean Near Wasm.Near

structure NonceRequest where
  configDir : String
  protocolVersion : Nat
  nonce : Nat
  currentNonce : Nat
  blockHeight : Option Nat
  nonceMode : String
  deriving FromJson

def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  let request : NonceRequest ← match Json.parse line >>= fromJson? with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  unless 84 ≤ request.protocolVersion && request.protocolVersion ≤ 86 do
    throw (IO.userError "nonce reference supports versions 84 through 86")
  unless (request.nonce :: request.currentNonce :: request.blockHeight.toList).all (· < 2 ^ 64) do
    throw (IO.userError "nonce context exceeds u64")
  let mode ← match request.nonceMode with
    | "monotonic" => pure NonceMode.monotonic
    | "strict" => pure NonceMode.strict
    | _ => throw (IO.userError "unknown nonce mode")
  let cfg ← RuntimeConfig.load request.configDir request.protocolVersion
  let result := if mode = .strict ∧ cfg.strictNonceEnabled = false then
      Except.error RuntimeError.invalidTransactionVersion
    else verifyNonce request.nonce request.currentNonce request.blockHeight mode
  let json := match result with
    | .ok () => Json.mkObj [("error", Json.null)]
    | .error .invalidTransactionVersion => Json.mkObj [("error", toJson "invalidTransactionVersion")]
    | .error (.invalidNonce nonce current) => Json.mkObj [
      ("error", toJson "invalidNonce"), ("nonce", toJson nonce), ("currentNonce", toJson current)]
    | .error (.nonceTooLarge nonce upper) => Json.mkObj [
      ("error", toJson "nonceTooLarge"), ("nonce", toJson nonce), ("upperBound", toJson upper)]
    | .error error => Json.mkObj [("unexpectedError", toJson error.message)]
  IO.println json.compress
