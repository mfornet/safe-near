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

def statusJson : ExecutionStatus → Json
  | .successValue value => obj [kind "successValue", ("value", bytesJson value)]
  | .successReceiptId id => obj [kind "successReceiptId", ("receiptId", toJson id)]
  | .failure error =>
    obj [kind "failure", ("error", toJson (reprStr error)), ("message", toJson error.message)]

def outcomeJson (pair : ReceiptId × ExecutionOutcome) : Json :=
  let (id, outcome) := pair
  obj
    [("id", toJson id),
      ("outcome",
        obj
          [("executorId", toJson outcome.executorId), ("status", statusJson outcome.status),
            ("logs", toJson outcome.logs), ("receiptIds", toJson outcome.receiptIds),
            ("gasBurnt", toJson outcome.gasBurnt),
            ("tokensBurnt", toJson (toString outcome.tokensBurnt))])]

def snapshotFields (s : Snapshot) : List (String × Json) :=
  [("state", stateJson s.state), ("pendingReceipts", toJson (s.pending.map receiptJson))]

def applyJson (s : Snapshot) (r : ApplyResult) : Json :=
  obj
    (snapshotFields s ++
      [("outcomes", toJson (r.outcomes.map outcomeJson)),
        ("outgoingReceipts", toJson (r.outgoing.map receiptJson)),
        ("tokensBurnt", toJson (toString r.tokensBurnt)),
        ("issue",
          toJson
            (r.issue.map fun (id, issue) =>
              obj
                [("receiptId", toJson id), ("error", toJson (reprStr issue)),
                  ("message", toJson issue.message)]))])

end ChainReplay
