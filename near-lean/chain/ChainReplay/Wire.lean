import NearChain.History
import NearRuntime.Epoch
import Wasm.Binary
import NearRuntime.StateEncoding

/-! JSON transport for the trusted chain manipulator. This preserves every
represented state/receipt field. Code hashes name an externally verified code
catalogue; signatures, consensus and byte-to-WAT correspondence remain external. -/

namespace ChainReplay

open Lean Wasm.Near Near

abbrev Result :=
  Except String

def field [FromJson α] (j : Json) (name : String) : Result α :=
  j.getObjValAs? α name

/-- An absent field reads as `null`/`none`, so that older requests stay valid. -/
def optionalField [FromJson α] (j : Json) (name : String) : Result (Option α) :=
  match j.getObjVal? name with
  | .error _ => pure none
  | .ok .null => pure none
  | .ok value => (fromJson? value : Except String α).map some

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
  | "gasKeyFullAccess" =>
    object j ["kind", "balance", "numNonces"]
    pure (.gasKeyFullAccess (← amount j "balance") (← field j "numNonces"))
  | "gasKeyFunctionCall" =>
    object j ["kind", "balance", "numNonces", "allowance", "receiverId", "methodNames"]
    let allowance : Option String ← field j "allowance"
    pure
        (.gasKeyFunctionCall (← amount j "balance") (← field j "numNonces") (← allowance.mapM balance)
          (← field j "receiverId") (← field j "methodNames"))
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

/-- The code for deployed bytes. Bytes a contract deploys from its own memory appear in no input, so
bytes outside the catalogue are decoded here exactly as `loadCatalogue` decodes its entries. -/
def codeOf (codes : Catalogue) (blob : Near.Bytes) : ContractCode :=
  match codes.find? (·.bytes == blob) with
  | some entry => entry.code
  | none =>
    let hash := Near.StateEncoding.base58 (Near.Sha256.hash blob)
    match Wasm.Binary.decode (ByteArray.mk blob.toArray) with
    | .ok module => { module, size := blob.length, hash }
    | .error e =>
      { module := default
        size := blob.length
        hash
        decodeIssue := some (.interpreterError s!"deployed bytes do not decode: {e.message}") }

/-- A global contract identifier: exactly one of the hash and the deploying account. -/
def globalIdentifier (j : Json) : Result Wasm.GlobalContractId := do
  object j ["codeHash", "accountId"]
  match j.getObjVal? "codeHash", j.getObjVal? "accountId" with
  | .ok _, .error _ => pure (.codeHash (← byteField j "codeHash"))
  | .error _, .ok _ => pure (.accountId (← byteField j "accountId"))
  | _, _ => throw "a global contract identifier needs exactly one of codeHash and accountId"

/-- Actions, with the actions a delegate action carries (not nested further). -/
partial def action (codes : Catalogue) (j : Json) : Result Action := do
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
  | "useGlobalContract" =>
    object j ["kind", "codeHash", "accountId"]
    match j.getObjVal? "codeHash", j.getObjVal? "accountId" with
    | .ok _, .error _ =>
      pure (.useGlobalContract (.codeHash (← byteField j "codeHash")))
    | .error _, .ok _ =>
      pure (.useGlobalContract (.accountId (← byteField j "accountId")))
    | _, _ =>
      throw "useGlobalContract needs exactly one of codeHash and accountId"
  | "deployGlobalContract" =>
    object j ["kind", "codeHash", "mode"]
    let mode : String ← field j "mode"
    pure
        (.deployGlobalContract (← codeByHash codes (← field j "codeHash"))
          (← match mode with
            | "codeHash" => pure .codeHash
            | "accountId" => pure .accountId
            | _ => throw s!"unknown global contract deploy mode: {mode}"))
  | "transferToGasKey" =>
    object j ["kind", "publicKey", "deposit"]
    pure (.transferToGasKey (← byteField j "publicKey") (← amount j "deposit"))
  | "withdrawFromGasKey" =>
    object j ["kind", "publicKey", "amount"]
    pure (.withdrawFromGasKey (← byteField j "publicKey") (← amount j "amount"))
  | "delegate" =>
    object j ["kind", "v2", "senderId", "receiverId", "actions", "nonce", "nonceIndex", "maxBlockHeight",
      "publicKey", "signature"]
    let inner : List Json ← field j "actions"
    let nonceIndex : Option Nat ← field j "nonceIndex"
    pure
        (.delegate (← field j "senderId") (← field j "receiverId") (← inner.mapM (action codes))
          (← u64 j "nonce") nonceIndex (← u64 j "maxBlockHeight") (← byteField j "publicKey")
          (← byteField j "signature") (← field j "v2"))
  | _ =>
    throw s!"unknown action: {kind}"

def transaction (codes : Catalogue) (j : Json) : Result Transaction := do
  object j ["version", "signerId", "publicKey", "nonce", "nonceMode", "receiverId", "actions"]
  let version : Nat ←
    match j.getObjVal? "version" with
    | .error _ =>
      pure 0
    | .ok value =>
      fromJson? value
  unless version ≤ 1 do
    throw "unsupported transaction envelope tag"
  let mode : String ←
    match j.getObjVal? "nonceMode" with
    | .error _ =>
      pure "monotonic"
    | .ok value =>
      fromJson? value
  let nonceMode ←
    match mode with
    | "monotonic" =>
      pure NonceMode.monotonic
    | "strict" =>
      pure NonceMode.strict
    | _ =>
      throw "unknown transaction nonce mode"
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
        object payload ["kind", "dataId", "data", "resumeDataId"]
        let data : Option (List Nat) ← field payload "data"
        let resume : Option (List Nat) ← optionalField payload "resumeDataId"
        pure
            (.data
              { dataId := ← field payload "dataId", data := ← data.mapM bytes,
                resumeDataId := ← resume.mapM bytes })
    | "globalDistribution" =>
      do
        object payload ["kind", "id", "targetShard", "alreadyDelivered", "codeHash", "nonce"]
        pure
            (.globalDistribution
              { id := ← globalIdentifier (← field payload "id")
                targetShard := ← field payload "targetShard"
                alreadyDelivered := ← field payload "alreadyDelivered"
                code := ← codeByHash codes (← field payload "codeHash")
                nonce := ← u64 payload "nonce" })
    | "action" =>
      do
        object payload
            ["kind", "signerId", "signerPublicKey", "gasPrice", "outputDataReceivers",
              "inputDataIds", "actions", "yieldDataId"]
        let outputs : List (Nat × String) ← field payload "outputDataReceivers"
        let actions : List Json ← field payload "actions"
        let yieldId : Option (List Nat) ← optionalField payload "yieldDataId"
        pure
            (.action
              { signerId := ← field payload "signerId"
                signerPublicKey := ← byteField payload "signerPublicKey"
                gasPrice := ← amount payload "gasPrice"
                outputDataReceivers :=
                  outputs.map fun (dataId, receiverId) => { dataId, receiverId }
                inputDataIds := ← field payload "inputDataIds"
                yieldDataId := ← yieldId.mapM bytes
                actions := ← actions.mapM (action codes) })
    | _ =>
      throw s!"unknown receipt: {kind}"
  pure {
        predecessorId := ← field j "predecessorId"
        receiverId := ← field j "receiverId"
        receiptId := ← field j "receiptId"
        receipt := value }

def account (codes : Catalogue) (j : Json) : Result Account := do
  object j ["amount", "locked", "codeHash", "storageUsage", "global", "versionTwo"]
  let hash : Option String ← field j "codeHash"
  let global : Option Json ← optionalField j "global"
  let versionTwo : Option Bool ← optionalField j "versionTwo"
  pure {
        amount := ← amount j "amount"
        locked := ← amount j "locked"
        storageUsage := ← u64 j "storageUsage"
        code := ← hash.mapM (codeByHash codes)
        global := ← global.mapM globalIdentifier
        versionTwo := versionTwo.getD false }

def state (codes : Catalogue) (j : Json) : Result ChainState := do
  object j
      ["accounts", "accessKeys", "storage", "postponed", "pendingDataCount", "postponedByData",
        "receivedData", "delayed", "nextId", "globalCode", "globalNonces", "gasKeyNonces", "yieldIndices",
        "yieldTimeouts", "yieldReceipts", "yieldStatus"]
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
  let globalCode : List (Json × String) := (← optionalField j "globalCode").getD []
  let globalNonces : List (Json × Nat) := (← optionalField j "globalNonces").getD []
  let gasKeyNonces : List (String × List Nat × Nat × Nat) := (← optionalField j "gasKeyNonces").getD []
  let yieldIndices : Option (Nat × Nat) ← optionalField j "yieldIndices"
  let yieldTimeouts : List (Nat × String × List Nat × Nat) := (← optionalField j "yieldTimeouts").getD []
  let yieldReceipts : List (String × List Nat × Json) := (← optionalField j "yieldReceipts").getD []
  let yieldStatus : List (String × List Nat × String) := (← optionalField j "yieldStatus").getD []
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
        globalCode :=
          ← globalCode.mapM fun (id, label) => do pure (← globalIdentifier id, ← codeByHash codes label)
        globalNonces := ← globalNonces.mapM fun (id, nonce) => do pure (← globalIdentifier id, nonce)
        gasKeyNonces :=
          ← gasKeyNonces.mapM fun (id, pk, lane, nonce) => do pure ((id, ← bytes pk, lane), nonce)
        yieldIndices
        yieldTimeouts :=
          ← yieldTimeouts.mapM fun (index, account, dataId, expiresAt) => do
              pure (index, { account, dataId := ← bytes dataId, expiresAt })
        yieldReceipts :=
          ← yieldReceipts.mapM fun (account, dataId, r) => do pure ((account, ← bytes dataId), ← receipt codes r)
        yieldStatus :=
          ← yieldStatus.mapM fun (account, dataId, status) => do
              pure ((account, ← bytes dataId),
                ← match status with
                  | "yielded" => pure YieldStatus.yielded
                  | "resumeInitiated" => pure YieldStatus.resumeInitiated
                  | _ => throw s!"unknown yield status: {status}")
        nextId := ← field j "nextId" }

/-- An object of decimal balances by account id. -/
def stakeTable (j : Json) : Result (List (String × Nat)) := do
  (← j.getObj?).toList.mapM fun (name, value) => do
    let text : String ← fromJson? value
    pure (name, ← balance text)

/-- `EpochInfoProvider`'s answers for the chunk. -/
def epochInfo (j : Json) : Result Near.EpochInfo := do
  object j ["minimumStake", "totalStake", "validators"]
  pure { minimumStake := ← amount j "minimumStake", totalStake := ← amount j "totalStake"
         validators := ← stakeTable (← field j "validators") }

/-- The `ValidatorAccountsUpdate` of an epoch's first chunk. -/
def validatorUpdate (j : Json) : Result Near.ValidatorAccountsUpdate := do
  object j ["stakeInfo", "validatorRewards", "lastProposals", "protocolTreasuryAccountId"]
  pure { stakeInfo := ← stakeTable (← field j "stakeInfo")
         validatorRewards := ← stakeTable (← field j "validatorRewards")
         lastProposals := ← stakeTable (← field j "lastProposals")
         protocolTreasury := ← optionalField j "protocolTreasuryAccountId" }

/-- The epoch-boundary update a block's JSON carries, if any. -/
def blockValidatorUpdate (j : Json) : Result (Option Near.ValidatorAccountsUpdate) :=
  match j.getObjVal? "validatorAccountsUpdate" with
  | .error _ | .ok .null => pure none
  | .ok value => do pure (some (← validatorUpdate value))

def block (codes : Catalogue) (j : Json) : Result Block := do
  object j
      ["blockHeight", "blockTimestamp", "epochHeight", "gasPrice", "gasLimit", "randomSeed",
        "transactions", "incomingIndices", "chainId", "shardId", "shardIds", "epochInfo",
        "validatorAccountsUpdate"]
  let epoch : Near.EpochInfo ← match j.getObjVal? "epochInfo" with
    | .error _ | .ok .null => pure {}
    | .ok value => epochInfo value
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
            randomSeed := seed
            chainId := (← optionalField j "chainId").getD ""
            shardId := (← optionalField j "shardId").getD 0
            shardIds := (← optionalField j "shardIds").getD [0]
            epochInfo := epoch }
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
    let _ : String := watPath
    let module ← IO.ofExcept ((Wasm.Binary.decode raw).mapError (·.message))
    if codes.any (fun entry => entry.code.hash == hash || entry.bytes == raw.toList) then
      throw (IO.userError "duplicate catalogue hash or bytes")
    codes := codes ++ [{ bytes := raw.toList, code := { module, size := raw.size, hash } }]
  pure codes

end ChainReplay
