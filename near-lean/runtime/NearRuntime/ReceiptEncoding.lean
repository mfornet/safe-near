import NearRuntime.StateEncoding
import NearRuntime.NativeIdentity

/-! Ordinary V0 receipts with legacy or V2 action payloads. Hash identities are explicit initial
inputs or derived by NativeIdentity; no model counter is serialized as a hash.
This does not encode delayed-queue wrappers, gas keys or yielded receipts. -/
namespace Near.ReceiptEncoding

open EncodingPrimitives

inductive ActionFormat
  | legacy
  | v2
  deriving BEq

private def account (id : AccountId) : Except String Bytes := do
  unless Wasm.Near.validAccountIdBytes id.toUTF8.toList do throw "invalid account id"
  string id

/-- A delegate action's nonce (`TransactionNonce`): plain, or a gas key lane. -/
private def delegateNonce (v2 : Bool) (nonce : Nat) (index : Option Nat) : Except String Bytes := do
  if v2 then
    match index with
    | none => return [0] ++ (← unsigned 8 nonce)
    | some lane => return [1] ++ (← unsigned 8 nonce) ++ (← unsigned 2 lane)
  else
    unless index.isNone do throw "a V1 delegate action has no nonce lane"
    unsigned 8 nonce

/-- The fields of a delegate action around its encoded inner actions. -/
def delegateFields (v2 : Bool) (sender receiver : AccountId) (count : Nat) (body : Bytes) (nonce : Nat)
    (nonceIndex : Option Nat) (maxHeight : Nat) (key : PublicKey) : Except String Bytes := do
  return (if v2 then [0] else []) ++ (← account sender) ++ (← account receiver)
    ++ (← unsigned 4 count) ++ body ++ (← delegateNonce v2 nonce nonceIndex) ++ (← unsigned 8 maxHeight)
    ++ (← StateEncoding.publicKey key)

mutual
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
  | .useGlobalContract (.codeHash hash) => do
    unless hash.length == 32 do throw "code hash is not 32 bytes"
    return [10, 0] ++ hash
  | .useGlobalContract (.accountId id) => do
    unless Wasm.Near.validAccountIdBytes id do throw "invalid account id"
    return [10, 1] ++ (← vector id)
  | .deployGlobalContract code mode => do
    let some bytes := Assoc.lookup codes code.hash | throw "code bytes absent from catalogue"
    unless bytes.length == code.size && StateEncoding.base58 (Sha256.hash bytes) == code.hash do
      throw "global deployment code identity mismatch"
    return [9] ++ (← vector bytes) ++ [match mode with | .codeHash => 0 | .accountId => 1]
  | .transferToGasKey key deposit => do
    return [12] ++ (← StateEncoding.publicKey key) ++ (← unsigned 16 deposit)
  | .withdrawFromGasKey key amount => do
    return [13] ++ (← StateEncoding.publicKey key) ++ (← unsigned 16 amount)
  | .delegate sender receiver inner nonce nonceIndex maxHeight key signature v2 => do
    let body ← actionList codes inner
    return [if v2 then 14 else 8] ++
      (← delegateFields v2 sender receiver inner.length body nonce nonceIndex maxHeight key) ++ signature

def actionList (codes : List (String × Bytes)) : List Action → Except String Bytes
  | [] => pure []
  | a :: rest => do return (← action codes a) ++ (← actionList codes rest)
end

/-- The signed part of a delegate action (`DelegateAction`, or the versioned `DelegateActionV2`
payload): the NEP-461 hash covers exactly these bytes behind the message discriminant. -/
def delegatePayload (codes : List (String × Bytes)) : Action → Except String Bytes
  | .delegate sender receiver inner nonce nonceIndex maxHeight key _ v2 => do
    delegateFields v2 sender receiver inner.length (← actionList codes inner) nonce nonceIndex maxHeight key
  | _ => throw "not a delegate action"

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
    unless format == .legacy || payload.resumeDataId.isSome do throw "action format supplied for data receipt"
    match payload.resumeDataId with
    | some dataId =>
      unless dataId.length == 32 do throw "yield data id is not 32 bytes"
      return header ++ [3] ++ dataId ++ (← receivedData payload.data)
    | none =>
      return header ++ [1] ++ (← NativeIdentity.resolve data payload.dataId) ++ (← receivedData payload.data)
  | .globalDistribution payload =>
    let some bytes := Assoc.lookup codes payload.code.hash | throw "distributed code bytes absent from catalogue"
    unless bytes.length == payload.code.size do throw "distributed code size disagrees with catalogue bytes"
    return header ++ [4, 1] ++ (← StateEncoding.globalIdentifier payload.id) ++ (← unsigned 8 payload.targetShard)
      ++ (← sequence (unsigned 8) payload.alreadyDelivered) ++ (← vector bytes) ++ (← unsigned 8 payload.nonce)
  | .action payload =>
    let outputs ← sequence (fun output => do
      return (← NativeIdentity.resolve data output.dataId) ++ (← account output.receiverId)) payload.outputDataReceivers
    -- Runtime promises use ActionV2 even at protocols 83–86. The represented
    -- runtime has no custom refund receiver; V2 therefore encodes refund_to=None.
    let tag : Bytes := if payload.yieldDataId.isSome then [6] else if format == .v2 then [5] else [0]
    let refund : Bytes := if format == .v2 || payload.yieldDataId.isSome then [0] else []
    -- A yield waits for exactly one data id, the one its creator was handed.
    let inputs ← match payload.yieldDataId with
      | some dataId => do
        unless dataId.length == 32 do throw "yield data id is not 32 bytes"
        pure ((← unsigned 4 1) ++ dataId)
      | none => sequence (NativeIdentity.resolve data) payload.inputDataIds
    return header ++ tag ++ (← account payload.signerId) ++ refund ++ (← StateEncoding.publicKey payload.signerPublicKey) ++
      (← unsigned 16 payload.gasPrice) ++ outputs ++ inputs ++ (← sequence (action codes) payload.actions)

end Near.ReceiptEncoding
