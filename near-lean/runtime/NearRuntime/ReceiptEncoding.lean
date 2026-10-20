import NearRuntime.StateEncoding
import NearRuntime.NativeIdentity

/-! Ordinary V0 receipts with legacy or V2 action payloads. Hash identities are explicit initial
inputs or derived by NativeIdentity; no model counter is serialized as a hash.
This does not encode delayed-queue wrappers, gas keys or yielded receipts. -/
namespace Near.ReceiptEncoding

inductive ActionFormat
  | legacy
  | v2
  deriving BEq

private def unsigned (width value : Nat) : Except String Bytes := do
  unless value < 2 ^ (8 * width) do throw s!"integer exceeds u{8 * width}"
  return (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

private def vector (bytes : Bytes) : Except String Bytes := do
  return (← unsigned 4 bytes.length) ++ bytes

private def string (text : String) : Except String Bytes := vector text.toUTF8.toList

private def account (id : AccountId) : Except String Bytes := do
  unless Wasm.Near.validAccountIdBytes id.toUTF8.toList do throw "invalid account id"
  string id

private def sequence (encode : α → Except String Bytes) (values : List α) : Except String Bytes := do
  return (← unsigned 4 values.length) ++ (← values.mapM encode).flatten

def action (codes : List (String × Bytes)) : Action → Except String Bytes
  | .createAccount => pure [0]
  | .deployContract code => do
    let some bytes := Assoc.lookup codes code.hash | throw "code bytes absent from catalogue"
    unless bytes.length == code.size && StateEncoding.base58 (Sha256.hash bytes) == code.hash do
      throw "deployment code identity mismatch"
    return [1] ++ (← vector bytes)
  | .functionCall method args gas deposit => do
    return [2] ++ (← string method) ++ (← vector args) ++ (← unsigned 8 gas) ++ (← unsigned 16 deposit)
  | .transfer deposit => do return [3] ++ (← unsigned 16 deposit)
  | .stake amount key => do return [4] ++ (← unsigned 16 amount) ++ (← StateEncoding.publicKey key)
  | .addKey key access => do return [5] ++ (← StateEncoding.publicKey key) ++ (← StateEncoding.accessKey access)
  | .deleteKey key => do return [6] ++ (← StateEncoding.publicKey key)
  | .deleteAccount beneficiary => do return [7] ++ (← account beneficiary)

/-- Borsh `ReceivedData` wraps only Option<Vec<u8>>. None and Some(empty)
remain distinct native state values. -/
def receivedData : Option Bytes → Except String Bytes
  | none => pure [0]
  | some bytes => do return [1] ++ (← vector bytes)

def encode (receipts data : NativeIdentity.Bindings) (codes : List (String × Bytes))
    (format : ActionFormat) (value : Receipt) : Except String Bytes := do
  NativeIdentity.validate receipts
  NativeIdentity.validate data
  let header := (← account value.predecessorId) ++ (← account value.receiverId) ++
    (← NativeIdentity.resolve receipts value.receiptId)
  match value.receipt with
  | .data payload =>
    unless format == .legacy do throw "action format supplied for data receipt"
    return header ++ [1] ++ (← NativeIdentity.resolve data payload.dataId) ++ (← receivedData payload.data)
  | .action payload =>
    let outputs ← sequence (fun output => do
      return (← NativeIdentity.resolve data output.dataId) ++ (← account output.receiverId)) payload.outputDataReceivers
    -- Runtime promises use ActionV2 even at protocols 83–86. The represented
    -- runtime has no custom refund receiver; V2 therefore encodes refund_to=None.
    let tag : Bytes := if format == .v2 then [5] else [0]
    let refund : Bytes := if format == .v2 then [0] else []
    return header ++ tag ++ (← account payload.signerId) ++ refund ++ (← StateEncoding.publicKey payload.signerPublicKey) ++
      (← unsigned 16 payload.gasPrice) ++ outputs ++
      (← sequence (NativeIdentity.resolve data) payload.inputDataIds) ++ (← sequence (action codes) payload.actions)

end Near.ReceiptEncoding
