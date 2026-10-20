import NearChain
import Interpreter.Wasm.Decoder.Wat

/-! JSON transport for the trusted chain manipulator. This preserves every
represented state/receipt field. Code hashes name an externally verified code
catalogue; signatures, consensus and byte-to-WAT correspondence remain external. -/

namespace ChainReplay

open Lean Wasm.Near Near

abbrev Result :=
  Except String

def field [FromJson α] (j : Json) (name : String) : Result α :=
  j.getObjValAs? α name

def object (j : Json) (allowed : List String) : Result Unit := do
  let values ← j.getObj?
  for (name, _) in values.toList do
    unless allowed.contains name do
      throw s!"unknown field: {name}"

def unique [BEq α] (name : String) (values : List α) : Result Unit := do
  unless values.eraseDups.length == values.length do
    throw s!"duplicate {name}"

def bounded (bits value : Nat) : Result Nat :=
  if value < 2 ^ bits then pure value else throw s!"integer exceeds u{bits}"

def u64 (j : Json) (name : String) : Result Nat := do
  bounded 64 (← field j name)

def balance (text : String) : Result Nat := do
  unless !text.isEmpty && text.toList.all Char.isDigit do
    throw "invalid decimal balance"
  let some value := text.toNat? | throw "invalid decimal balance"
  bounded 128 value

def amount (j : Json) (name : String) : Result Nat := do
  balance (← field j name)

def bytes (ns : List Nat) : Result Near.Bytes :=
  ns.mapM fun n => do
    unless n < 256 do
      throw s!"invalid byte: {n}"
    pure (UInt8.ofNat n)

def byteField (j : Json) (name : String) : Result Near.Bytes := do
  bytes (← field j name)

def permission (j : Json) : Result Near.AccessKeyPermission := do
  let kind : String ← field j "kind"
  match kind with
  | "fullAccess" =>
    object j ["kind"]
    pure .fullAccess
  | "functionCall" =>
    object j ["kind", "allowance", "receiverId", "methodNames"]
    let allowance : Option String ← field j "allowance"
    pure
        (.functionCall (← allowance.mapM balance) (← field j "receiverId")
          (← field j "methodNames"))
  | _ =>
    throw s!"unknown access key permission: {kind}"

def key (j : Json) : Result AccessKey := do
  object j ["nonce", "permission"]
  pure { nonce := ← u64 j "nonce", permission := ← permission (← field j "permission") }

structure LoadedCode where
  bytes : Near.Bytes
  code : ContractCode

abbrev Catalogue :=
  List LoadedCode

def codeByHash (codes : Catalogue) (hash : String) : Result ContractCode :=
  match codes.find? (·.code.hash == hash) with
  | some entry => pure entry.code
  | none => throw s!"code hash absent from catalogue: {hash}"

def codeOf (codes : Catalogue) (blob : Near.Bytes) : ContractCode :=
  match codes.find? (·.bytes == blob) with
  | some entry => entry.code
  | none =>
    { module := default
      size := blob.length
      hash := ""
      decodeIssue := some (.interpreterError "deployed bytes absent from replay code catalogue") }

def action (codes : Catalogue) (j : Json) : Result Action := do
  let kind : String ← field j "kind"
  match kind with
  | "createAccount" =>
    object j ["kind"]
    pure .createAccount
  | "deployContract" =>
    object j ["kind", "codeHash"]
    pure (.deployContract (← codeByHash codes (← field j "codeHash")))
  | "functionCall" =>
    object j ["kind", "methodName", "args", "gas", "deposit"]
    pure
        (.functionCall (← field j "methodName") (← byteField j "args") (← u64 j "gas")
          (← amount j "deposit"))
  | "transfer" =>
    object j ["kind", "deposit"]
    pure (.transfer (← amount j "deposit"))
  | "stake" =>
    object j ["kind", "stake", "publicKey"]
    pure (.stake (← amount j "stake") (← byteField j "publicKey"))
  | "addKey" =>
    object j ["kind", "publicKey", "accessKey"]
    pure (.addKey (← byteField j "publicKey") (← key (← field j "accessKey")))
  | "deleteKey" =>
    object j ["kind", "publicKey"]
    pure (.deleteKey (← byteField j "publicKey"))
  | "deleteAccount" =>
    object j ["kind", "beneficiaryId"]
    pure (.deleteAccount (← field j "beneficiaryId"))
  | _ =>
    throw s!"unknown action: {kind}"

def transaction (codes : Catalogue) (j : Json) : Result Transaction := do
  object j ["version", "signerId", "publicKey", "nonce", "nonceMode", "receiverId", "actions"]
  let version : Nat ← match j.getObjVal? "version" with
    | .error _ => pure 0
    | .ok value => fromJson? value
  unless version ≤ 1 do throw "unsupported transaction envelope tag"
  let mode : String ← match j.getObjVal? "nonceMode" with
    | .error _ => pure "monotonic"
    | .ok value => fromJson? value
  let nonceMode ← match mode with
    | "monotonic" => pure NonceMode.monotonic
    | "strict" => pure NonceMode.strict
    | _ => throw "unknown transaction nonce mode"
  unless version == 1 || nonceMode == .monotonic do
    throw "V0 transactions have no strict nonce mode"
  let actions : List Json ← field j "actions"
  pure {
        version
        nonceMode
        signerId := ← field j "signerId"
        publicKey := ← byteField j "publicKey"
        nonce := ← u64 j "nonce"
        receiverId := ← field j "receiverId"
        actions := ← actions.mapM (action codes) }

def receipt (codes : Catalogue) (j : Json) : Result Receipt := do
  object j ["predecessorId", "receiverId", "receiptId", "receipt"]
  let payload : Json ← field j "receipt"
  let kind : String ← field payload "kind"
  let value ←
    match kind with
    | "data" =>
      do
        object payload ["kind", "dataId", "data"]
        let data : Option (List Nat) ← field payload "data"
        pure (.data { dataId := ← field payload "dataId", data := ← data.mapM bytes })
    | "action" =>
      do
        object payload
            ["kind", "signerId", "signerPublicKey", "gasPrice", "outputDataReceivers",
              "inputDataIds", "actions"]
        let outputs : List (Nat × String) ← field payload "outputDataReceivers"
        let actions : List Json ← field payload "actions"
        pure
            (.action
              { signerId := ← field payload "signerId"
                signerPublicKey := ← byteField payload "signerPublicKey"
                gasPrice := ← amount payload "gasPrice"
                outputDataReceivers :=
                  outputs.map fun (dataId, receiverId) => { dataId, receiverId }
                inputDataIds := ← field payload "inputDataIds"
                actions := ← actions.mapM (action codes) })
    | _ =>
      throw s!"unknown receipt: {kind}"
  pure {
        predecessorId := ← field j "predecessorId"
        receiverId := ← field j "receiverId"
        receiptId := ← field j "receiptId"
        receipt := value }

def account (codes : Catalogue) (j : Json) : Result Account := do
  object j ["amount", "locked", "codeHash", "storageUsage"]
  let hash : Option String ← field j "codeHash"
  pure {
        amount := ← amount j "amount"
        locked := ← amount j "locked"
        storageUsage := ← u64 j "storageUsage"
        code := ← hash.mapM (codeByHash codes) }

def state (codes : Catalogue) (j : Json) : Result ChainState := do
  object j
      ["accounts", "accessKeys", "storage", "postponed", "pendingDataCount", "postponedByData",
        "receivedData", "delayed", "nextId"]
  let accounts : List (String × Json) ← field j "accounts"
  unique "account" (accounts.map (·.1))
  let keys : List ((String × List Nat) × Json) ← field j "accessKeys"
  unique "access key" (keys.map (·.1))
  let storage : List (String × List (List Nat × List Nat)) ← field j "storage"
  unique "storage account" (storage.map (·.1))
  let storage ←
    storage.mapM fun (id, entries) => do
        unique "storage key" (entries.map (·.1))
        pure
            (id,
              ←
                entries.mapM fun (k, v) => do
                    pure (← bytes k, ← bytes v))
  let postponed : List (Nat × Json) ← field j "postponed"
  unique "postponed receipt" (postponed.map (·.1))
  let postponed ←
    postponed.mapM fun (id, j) => do
        let r ← receipt codes j
        unless id == r.receiptId do
          throw "postponed receipt id disagrees with its map key"
        pure (id, r)
  let pendingDataCount : List (Nat × Nat) ← field j "pendingDataCount"
  unique "pending data count" (pendingDataCount.map (·.1))
  let postponedByData : List (Nat × Nat) ← field j "postponedByData"
  unique "postponed data id" (postponedByData.map (·.1))
  let received : List (Nat × Option (List Nat)) ← field j "receivedData"
  unique "received data id" (received.map (·.1))
  let delayed : List Json ← field j "delayed"
  pure {
        accounts :=
          ←
            accounts.mapM fun (id, j) => do
                pure (id, ← account codes j)
        accessKeys :=
          ←
            keys.mapM fun ((id, pk), j) => do
                pure ((id, ← bytes pk), ← key j)
        storage
        postponed
        pendingDataCount
        postponedByData
        receivedData :=
          ←
            received.mapM fun (id, data) => do
                pure (id, ← data.mapM bytes)
        delayed := ← delayed.mapM (receipt codes)
        nextId := ← field j "nextId" }

def block (codes : Catalogue) (j : Json) : Result Block := do
  object j
      ["blockHeight", "blockTimestamp", "epochHeight", "gasPrice", "gasLimit", "randomSeed",
        "transactions", "incomingIndices"]
  let gasLimit : Option Nat ← field j "gasLimit"
  let seed ← byteField j "randomSeed"
  unless seed.length == 32 do
    throw "randomSeed must contain 32 bytes"
  let positions : Option (List Nat) ← field j "incomingIndices"
  let transactions : List Json ← field j "transactions"
  pure {
        ap :=
          { blockHeight := ← u64 j "blockHeight"
            blockTimestamp := ← u64 j "blockTimestamp"
            epochHeight := ← u64 j "epochHeight"
            gasPrice := ← amount j "gasPrice"
            gasLimit := ← gasLimit.mapM (bounded 64)
            randomSeed := seed }
        txs := ← transactions.mapM (transaction codes)
        receipts := positions.elim .all .indices }

def loadCatalogue (values : List Json) : IO Catalogue := do
  let mut codes : Catalogue := []
  for value in values do
    let (hash, codePath, watPath) ←
      IO.ofExcept do
          object value ["hash", "codePath", "watPath"]
          pure (← field value "hash", ← field value "codePath", ← field value "watPath")
    if (hash : String).isEmpty then
      throw (IO.userError "empty catalogue hash")
    let raw ← IO.FS.readBinFile (codePath : String)
    let text ← IO.FS.readFile (watPath : String)
    let module ← IO.ofExcept (Wasm.Decoder.Wat.decode text)
    if codes.any (fun entry => entry.code.hash == hash || entry.bytes == raw.toList) then
      throw (IO.userError "duplicate catalogue hash or bytes")
    codes := codes ++ [{ bytes := raw.toList, code := { module, size := raw.size, hash } }]
  pure codes

end ChainReplay
