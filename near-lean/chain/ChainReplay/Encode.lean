import ChainReplay.Wire

namespace ChainReplay

open Lean Near

def obj :=
  Json.mkObj

def kind (name : String) : String × Json :=
  ("kind", toJson name)

def bytesJson (value : Near.Bytes) : Json :=
  toJson (value.map UInt8.toNat)

def permissionJson : AccessKeyPermission → Json
  | .fullAccess => obj [kind "fullAccess"]
  | .functionCall allowance receiver methods =>
    obj
      [kind "functionCall", ("allowance", toJson (allowance.map toString)),
        ("receiverId", toJson receiver), ("methodNames", toJson methods)]

def keyJson (key : AccessKey) : Json :=
  obj [("nonce", toJson key.nonce), ("permission", permissionJson key.permission)]

def actionJson : Action → Json
  | .createAccount => obj [kind "createAccount"]
  | .deployContract code => obj [kind "deployContract", ("codeHash", toJson code.hash)]
  | .functionCall method args gas deposit =>
    obj
      [kind "functionCall", ("methodName", toJson method), ("args", bytesJson args),
        ("gas", toJson gas), ("deposit", toJson (toString deposit))]
  | .transfer deposit => obj [kind "transfer", ("deposit", toJson (toString deposit))]
  | .stake stake pk =>
    obj [kind "stake", ("stake", toJson (toString stake)), ("publicKey", bytesJson pk)]
  | .addKey pk key => obj [kind "addKey", ("publicKey", bytesJson pk), ("accessKey", keyJson key)]
  | .deleteKey pk => obj [kind "deleteKey", ("publicKey", bytesJson pk)]
  | .deleteAccount beneficiary => obj [kind "deleteAccount", ("beneficiaryId", toJson beneficiary)]
  | .useGlobalContract (.codeHash hash) => obj [kind "useGlobalContract", ("codeHash", bytesJson hash)]
  | .useGlobalContract (.accountId id) => obj [kind "useGlobalContract", ("accountId", bytesJson id)]

def receiptJson (r : Receipt) : Json :=
  obj
    [("predecessorId", toJson r.predecessorId), ("receiverId", toJson r.receiverId),
      ("receiptId", toJson r.receiptId),
      ("receipt",
        match r.receipt with
        | .data data =>
          obj
            [kind "data", ("dataId", toJson data.dataId),
              ("data", toJson (data.data.map bytesJson))]
        | .action action =>
          obj
            [kind "action", ("signerId", toJson action.signerId),
              ("signerPublicKey", bytesJson action.signerPublicKey),
              ("gasPrice", toJson (toString action.gasPrice)),
              ("inputDataIds", toJson action.inputDataIds),
              ("outputDataReceivers",
                toJson (action.outputDataReceivers.map fun d => (d.dataId, d.receiverId))),
              ("actions", toJson (action.actions.map actionJson))])]

def accountJson (a : Account) : Json :=
  obj
    [("amount", toJson (toString a.amount)), ("locked", toJson (toString a.locked)),
      ("storageUsage", toJson a.storageUsage), ("codeHash", toJson (a.code.map (·.hash)))]

/-- Preserve association-list order as well as every represented state field.
The shared code catalogue resolves each code label to its exact supplied module. -/
def stateJson (s : ChainState) : Json :=
  obj
    [("accounts", toJson (s.accounts.map fun (id, a) => (id, accountJson a))),
      ("accessKeys",
        toJson (s.accessKeys.map fun ((id, pk), key) => ((id, bytesJson pk), keyJson key))),
      ("storage",
        toJson
          (s.storage.map fun (id, entries) =>
            (id, entries.map fun (k, v) => (bytesJson k, bytesJson v)))),
      ("postponed", toJson (s.postponed.map fun (id, r) => (id, receiptJson r))),
      ("pendingDataCount", toJson s.pendingDataCount),
      ("postponedByData", toJson s.postponedByData),
      ("receivedData", toJson (s.receivedData.map fun (id, data) => (id, data.map bytesJson))),
      ("delayed", toJson (s.delayed.map receiptJson)), ("nextId", toJson s.nextId)]

def actionValidationErrorJson : ActionsValidationError → Json
  | .deleteActionMustBeFinal => obj [kind "DeleteActionMustBeFinal"]
  | .functionCallZeroAttachedGas => obj [kind "FunctionCallZeroAttachedGas"]
  | .unsuitableStakingKey key => obj [kind "UnsuitableStakingKey", ("public_key", bytesJson key)]
  | .integerOverflow => obj [kind "IntegerOverflow"]
  | .totalPrepaidGasExceeded total limit => obj [kind "TotalPrepaidGasExceeded", ("total_prepaid_gas", toJson total), ("limit", toJson limit)]
  | .totalNumberOfActionsExceeded count limit => obj [kind "TotalNumberOfActionsExceeded", ("total_number_of_actions", toJson count), ("limit", toJson limit)]
  | .totalNumberOfDeployActionsExceeded count limit => obj [kind "TotalNumberOfDeployActionsExceeded", ("number_of_deploy_actions", toJson count), ("limit", toJson limit)]
  | .addKeyMethodNamesNumberOfBytesExceeded total limit => obj [kind "AddKeyMethodNamesNumberOfBytesExceeded", ("total_number_of_bytes", toJson total), ("limit", toJson limit)]
  | .addKeyMethodNameLengthExceeded length limit => obj [kind "AddKeyMethodNameLengthExceeded", ("length", toJson length), ("limit", toJson limit)]
  | .invalidAccountId id => obj [kind "InvalidAccountId", ("account_id", toJson id)]
  | .contractSizeExceeded size limit => obj [kind "ContractSizeExceeded", ("size", toJson size), ("limit", toJson limit)]
  | .functionCallMethodNameLengthExceeded length limit => obj [kind "FunctionCallMethodNameLengthExceeded", ("length", toJson length), ("limit", toJson limit)]
  | .functionCallArgumentsLengthExceeded length limit => obj [kind "FunctionCallArgumentsLengthExceeded", ("length", toJson length), ("limit", toJson limit)]

/-- Structured semantic error fields are independent of Lean's pretty printer. -/
def runtimeErrorJson (executor : AccountId) : RuntimeError → Json
  | .actionsValidation error => obj [kind "actionsValidation", ("error", actionValidationErrorJson error)]
  | .newReceiptValidationError (.actionsValidation error) =>
    obj [kind "newReceiptValidationError", ("error", obj [kind "actionsValidation", ("error", actionValidationErrorJson error)])]
  | .newReceiptValidationError (.receiptSizeExceeded size limit) =>
    obj [kind "newReceiptValidationError", ("error", obj [kind "receiptSizeExceeded",
      ("size", toJson size), ("limit", toJson limit)])]
  | .accountAlreadyExists id => obj [kind "accountAlreadyExists", ("accountId", toJson id)]
  | .accountDoesNotExist id => obj [kind "accountDoesNotExist", ("accountId", toJson id)]
  | .createAccountNotAllowed id predecessor =>
    obj [kind "createAccountNotAllowed", ("accountId", toJson id), ("predecessorId", toJson predecessor)]
  | .createAccountOnlyByRegistrar id registrar predecessor =>
    obj [kind "createAccountOnlyByRegistrar", ("accountId", toJson id),
      ("registrarId", toJson registrar), ("predecessorId", toJson predecessor)]
  | .actorNoPermission id actor =>
    obj [kind "actorNoPermission", ("accountId", toJson id), ("actorId", toJson actor)]
  | .deleteKeyDoesNotExist id pk =>
    obj [kind "deleteKeyDoesNotExist", ("accountId", toJson id), ("publicKey", bytesJson pk)]
  | .addKeyAlreadyExists id pk =>
    obj [kind "addKeyAlreadyExists", ("accountId", toJson id), ("publicKey", bytesJson pk)]
  | .deleteAccountStaking id => obj [kind "deleteAccountStaking", ("accountId", toJson id)]
  | .lackBalanceForState id amount =>
    obj [kind "lackBalanceForState", ("accountId", toJson id), ("amount", toJson (toString amount))]
  | .triesToUnstake id => obj [kind "triesToUnstake", ("accountId", toJson id)]
  | .triesToStake id stake locked balance =>
    obj [kind "triesToStake", ("accountId", toJson id), ("stake", toJson (toString stake)),
      ("locked", toJson (toString locked)), ("balance", toJson (toString balance))]
  | .insufficientStake id => obj [kind "insufficientStake", ("accountId", toJson id)]
  | .functionCallError error =>
    let inner := match error with
      | .methodResolveError .methodEmptyName => obj [kind "methodResolveError", ("error", toJson "MethodEmptyName")]
      | .methodResolveError .methodNotFound => obj [kind "methodResolveError", ("error", toJson "MethodNotFound")]
      | .methodResolveError .methodInvalidSignature => obj [kind "methodResolveError", ("error", toJson "MethodInvalidSignature")]
      | .compilationError message =>
        if message == "CodeDoesNotExist" then
          obj [kind "compilationError", ("message", toJson message), ("accountId", toJson executor)]
        else obj [kind "compilationError", ("message", toJson message)]
      | .linkError _ | .hostError _ | .wasmTrap _ => obj [kind "executionError", ("message", toJson error.message)]
      | .internal message => obj [kind "internal", ("message", toJson message)]
      | .prepareError e => obj [kind "compilationError", ("prepareError", toJson e.name)]
      | .executionIssue issue => obj [kind "executionIssue", ("message", toJson issue.message)]
    obj [kind "functionCallError", ("error", inner)]
  | .deleteActionMustBeFinal => obj [kind "deleteActionMustBeFinal"]
  | .onlyImplicitAccountCreationAllowed id => obj [kind "onlyImplicitAccountCreationAllowed", ("accountId", toJson id)]
  | .deleteAccountWithLargeState id => obj [kind "deleteAccountWithLargeState", ("accountId", toJson id)]
  | .invalidSigner id => obj [kind "invalidSigner", ("accountId", toJson id)]
  | .invalidTransactionVersion => obj [kind "invalidTransactionVersion"]
  | .transactionSizeExceeded size limit => obj [kind "transactionSizeExceeded", ("size", toJson size), ("limit", toJson limit)]
  | .invalidNonce nonce current => obj [kind "invalidNonce", ("nonce", toJson nonce), ("currentNonce", toJson current)]
  | .nonceTooLarge nonce upper => obj [kind "nonceTooLarge", ("nonce", toJson nonce), ("upperBound", toJson upper)]
  | .invalidAccessKey message => obj [kind "invalidAccessKey", ("reason", toJson message)]
  | .accessKeyNotFound id pk => obj [kind "invalidAccessKey", ("reason", toJson "AccessKeyNotFound"),
      ("accountId", toJson id), ("publicKey", bytesJson pk)]
  | .receiverMismatch txReceiver keyReceiver => obj [kind "invalidAccessKey", ("reason", toJson "ReceiverMismatch"),
      ("txReceiver", toJson txReceiver), ("keyReceiver", toJson keyReceiver)]
  | .methodNameMismatch method => obj [kind "invalidAccessKey", ("reason", toJson "MethodNameMismatch"),
      ("methodName", toJson method)]
  | .notEnoughAllowance id pk allowance cost => obj [kind "invalidAccessKey", ("reason", toJson "NotEnoughAllowance"),
      ("accountId", toJson id), ("publicKey", bytesJson pk),
      ("allowance", toJson (toString allowance)), ("cost", toJson (toString cost))]
  | .notEnoughBalance id balance cost =>
    obj [kind "notEnoughBalance", ("accountId", toJson id), ("balance", toJson (toString balance)), ("cost", toJson (toString cost))]
  | .invalidReceiver id => obj [kind "invalidReceiver", ("accountId", toJson id)]
  | .contractSizeExceeded size limit => obj [kind "contractSizeExceeded", ("size", toJson size), ("limit", toJson limit)]
  | .tooManyActions count limit => obj [kind "tooManyActions", ("count", toJson count), ("limit", toJson limit)]
  | .executionIssue issue => obj [kind "executionIssue", ("message", toJson issue.message)]

def statusJson (status : ExecutionStatus) (index : Option Nat := none) (executor : AccountId := "") : Json :=
  match status with
  | .successValue value => obj [kind "successValue", ("value", bytesJson value)]
  | .successReceiptId id => obj [kind "successReceiptId", ("receiptId", toJson id)]
  | .failure error =>
    obj [kind "failure", ("error", toJson (reprStr error)), ("message", toJson error.message),
      ("details", runtimeErrorJson executor error), ("actionIndex", toJson index)]

def outcomeJson (pair : ReceiptId × ExecutionOutcome) : Json :=
  let (id, outcome) := pair
  obj
    [("id", toJson id),
      ("outcome",
        obj
          [("executorId", toJson outcome.executorId), ("status", statusJson outcome.status outcome.failureIndex outcome.executorId),
            ("logs", toJson outcome.logs), ("receiptIds", toJson outcome.receiptIds),
            ("gasBurnt", toJson outcome.gasBurnt),
            ("tokensBurnt", toJson (toString outcome.tokensBurnt))])]

def snapshotFields (s : Snapshot) : List (String × Json) :=
  [("state", stateJson s.state), ("pendingReceipts", toJson (s.pending.map receiptJson))]

def transactionSizeJson (cfg : Wasm.Near.RuntimeConfig) (tx : Transaction) : Json :=
  obj [("bodySize", toJson tx.bodySize),
    ("wireSize", toJson (tx.signatureSize?.map (tx.bodySize + ·))),
    ("sizeForLimits", toJson (tx.sizeForLimits? cfg))]

def applyJson (cfg : Wasm.Near.RuntimeConfig) (transactions : List Transaction) (s : Snapshot) (r : ApplyResult) : Json :=
  obj
    (snapshotFields s ++
      [("transactionSizes", toJson (transactions.map (transactionSizeJson cfg))),
        ("outcomes", toJson (r.outcomes.map outcomeJson)),
        ("outgoingReceipts", toJson (r.outgoing.map receiptJson)),
        ("tokensBurnt", toJson (toString r.tokensBurnt)),
        ("subsidizedAmount", toJson (toString r.subsidizedAmount)),
        ("issue",
          toJson
            (r.issue.map fun (id, issue) =>
              obj
                [("receiptId", toJson id), ("error", toJson (reprStr issue)),
                  ("message", toJson issue.message)]))])

end ChainReplay
