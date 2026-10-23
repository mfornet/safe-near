import NearVM
import Wasm.Wat

open Lean Wasm Wasm.Near

namespace Replay

/-- Shared wire format with tools/runtime-conformance. Numeric byte arrays
are checked before conversion; large balances use decimal strings. -/
structure Request where
  validateActionMethodUtf8 : Bool := false
  codePath : String
  watPath : String
  configDir : String
  protocolVersion : Nat
  method : String
  currentAccountId : String
  signerAccountId : String
  signerAccountPk : List Nat
  predecessorAccountId : String
  input : List Nat
  promiseResults : List (Option (List Nat))
  blockHeight : Nat
  blockTimestamp : Nat
  epochHeight : Nat
  accountBalance : String
  accountLockedBalance : String
  storageUsage : Nat
  attachedDeposit : String
  prepaidGas : Nat
  randomSeed : List Nat
  view : Bool
  outputDataReceivers : List String
  storage : List (List Nat × List Nat)
  deriving FromJson

def checkedBytes (values : List Nat) : Except String (List UInt8) :=
  values.mapM fun value =>
    if value < 256 then pure (UInt8.ofNat value) else throw s!"invalid byte: {value}"

def checkedBalance (text : String) : Except String Nat := do
  let some value := text.toNat? | throw "invalid decimal balance"
  if value < 2 ^ 128 then pure value else throw "balance exceeds u128"

def inputOf (cfg : RuntimeConfig) (r : Request) :
    Except String (VMContext × List (List UInt8 × List UInt8)) := do
  unless [r.blockHeight, r.blockTimestamp, r.epochHeight, r.storageUsage, r.prepaidGas].all
      (· < 2 ^ 64) do throw "context exceeds u64"
  let storage ← r.storage.mapM fun (key, value) => do
    pure (← checkedBytes key, ← checkedBytes value)
  unless (storage.map (·.1)).eraseDups.length == storage.length do throw "duplicate storage key"
  let promiseResults ← r.promiseResults.mapM fun result => do
    match result with
    | none => pure PromiseResult.failed
    | some bytes => pure (PromiseResult.successful (← checkedBytes bytes))
  let ctx : VMContext := {
    validateActionMethodUtf8 := r.validateActionMethodUtf8
    currentAccountId := r.currentAccountId.toUTF8.toList
    signerAccountId := r.signerAccountId.toUTF8.toList
    signerAccountPk := ← checkedBytes r.signerAccountPk
    predecessorAccountId := r.predecessorAccountId.toUTF8.toList
    input := ← checkedBytes r.input
    promiseResults
    blockHeight := r.blockHeight
    blockTimestamp := r.blockTimestamp
    epochHeight := r.epochHeight
    accountBalance := ← checkedBalance r.accountBalance
    accountLockedBalance := ← checkedBalance r.accountLockedBalance
    storageUsage := r.storageUsage
    attachedDeposit := ← checkedBalance r.attachedDeposit
    prepaidGas := r.prepaidGas
    randomSeed := ← checkedBytes r.randomSeed
    viewConfig := if r.view then some { maxGasBurnt := cfg.wasm.limits.maxGasBurnt } else none
    outputDataReceivers := r.outputDataReceivers.map (·.toUTF8.toList) }
  pure (ctx, storage)

def bytesJson (bytes : List UInt8) : Json := toJson (bytes.map UInt8.toNat)
def obj := Json.mkObj
def kind (name : String) : String × Json := ("kind", toJson name)

def permissionJson : AccessKeyPermission → Json
  | .fullAccess => obj [kind "fullAccess"]
  | .functionCall allowance receiver methods => obj [kind "functionCall",
      ("allowance", toJson (allowance.map toString)),
      ("receiverId", bytesJson receiver), ("methodNames", bytesJson methods)]

def actionJson : PromiseAction → Json
  | .createAccount => obj [kind "createAccount"]
  | .deployContract code => obj [kind "deployContract", ("code", bytesJson code)]
  | .functionCall method args amount gas => obj [kind "functionCall",
      ("method", bytesJson method), ("args", bytesJson args),
      ("deposit", toJson (toString amount)), ("gas", toJson gas.toNat)]
  | .transfer amount => obj [kind "transfer", ("deposit", toJson (toString amount))]
  | .stake amount pk => obj [kind "stake", ("stake", toJson (toString amount)), ("publicKey", bytesJson pk)]
  | .addKey pk nonce permission => obj [kind "addKey", ("publicKey", bytesJson pk),
      ("nonce", toJson nonce.toNat), ("permission", permissionJson permission)]
  | .deleteKey pk => obj [kind "deleteKey", ("publicKey", bytesJson pk)]
  | .deleteAccount beneficiary => obj [kind "deleteAccount", ("beneficiaryId", bytesJson beneficiary)]
  | .useGlobalContract (.codeHash hash) => obj [kind "useGlobalContract", ("codeHash", bytesJson hash)]
  | .useGlobalContract (.accountId id) => obj [kind "useGlobalContract", ("accountId", bytesJson id)]

def receiptJson (receipt : ReceiptSpec) : Json := obj [
  ("receiverId", bytesJson receipt.receiverId),
  ("dependencies", toJson receipt.dependencies),
  ("actions", toJson (receipt.actions.map actionJson))]

def returnJson : ReturnData → Json
  | .none => obj [kind "none"]
  | .value bytes => obj [kind "value", ("bytes", bytesJson bytes)]
  | .receiptIndex index => obj [kind "receipt", ("index", toJson index)]

def outcomeJson (outcome : VMOutcome) : Json :=
  let storage := outcome.storage.mergeSort (fun a b => bytesLe a.1 b.1)
  obj [
    ("balance", toJson (toString outcome.balance)),
    ("storageUsage", toJson outcome.storageUsage),
    ("returnData", returnJson outcome.returnData),
    ("gasBurnt", toJson outcome.burntGas), ("gasUsed", toJson outcome.usedGas),
    ("logs", toJson outcome.logs),
    ("storage", toJson (storage.map fun (k, v) => (k.map UInt8.toNat, v.map UInt8.toNat))),
    ("receipts", toJson (outcome.receipts.map receiptJson)),
    ("aborted", toJson (outcome.aborted.map (·.message))),
    ("issue", toJson (outcome.issue?.map (·.message))),
    ("subsidizedAmount", toJson (toString outcome.subsidizedAmount)),
    ("gasProfile", obj [
      ("ext", obj (outcome.gasProfile.ext.map fun (name, gas) => (name, toJson gas))),
      ("actionBurnt", toJson outcome.gasProfile.actionBurnt),
      ("wasm", toJson outcome.gasProfile.wasm)])]

def execute (request : Request) : IO Json := do
  if request.protocolVersion > 86 then throw (IO.userError "reference supports protocol versions through 86")
  let cfg ← RuntimeConfig.load request.configDir request.protocolVersion
  let (ctx, storage) ← match inputOf cfg request with
    | .ok input => pure input
    | .error error => throw (IO.userError error)
  let bytes ← IO.FS.readBinFile request.codePath
  let code ← match Binary.decode bytes with
    | .ok code => pure code
    | .error error => throw (IO.userError s!"Wasm decode failed: {error.message}")
  pure (outcomeJson (run cfg code bytes.size request.method ctx storage))

end Replay

def main : IO Unit := do
  let input ← (← IO.getStdin).getLine
  let request ← match Json.parse input >>= fromJson? with
    | .ok request => pure (request : Replay.Request)
    | .error error => throw (IO.userError s!"invalid execution request: {error}")
  IO.println (← Replay.execute request).compress
