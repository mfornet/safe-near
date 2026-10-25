import Lean.Data.Json
import NearNode.Network.Keys
import NearNode.Primitives.TransactionAccess
import NearNode.Chain.State
import NearNode.Chain.Types
import NearNode.Rpc.Base64

/-!
# The JSON of nearcore's views

`near-primitives::views` (`core/primitives/src/views.rs`) at the pinned nearcore, as `serde_json` writes
them: hashes, public keys and signatures as text (base58, `ed25519:` and `secp256k1:` prefixes), balances
(`u128`) as decimal strings, gas and nonces as numbers, bytes as standard base64, enums externally tagged.
Only the encoding of values lives here; what a request returns is decided in `NearNode.Rpc.Methods`.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Network Near.Node.Chain

/-- A natural number as a JSON number. -/
def jn (n : Nat) : Json :=
  Json.num (JsonNumber.fromNat n)

def jhash (h : CryptoHash) : Json :=
  Json.str (base58Encode h.bytes)

def jbal (b : Balance) : Json :=
  Json.str (toString b.val)

def jkey (k : PublicKey) : Json :=
  Json.str k.toText

def jacc (a : AccountId) : Json :=
  Json.str a.val

def jsig : Signature → Json
  | .ed25519 s => Json.str ("ed25519:" ++ base58Encode s)
  | .secp256k1 s => Json.str ("secp256k1:" ++ base58Encode s)
  | .mldsa65 s => Json.str ("mldsa65:" ++ base58Encode s)

def jbytes (b : ByteArray) : Json :=
  Json.str (base64Encode b)

def jarr {α : Type} (f : α → Json) (xs : Array α) : Json :=
  Json.arr (xs.map f)

def jopt {α : Type} (f : α → Json) : Option α → Json
  | some x => f x
  | none => Json.null

/-- `{"tag": value}`: an externally tagged enum variant. -/
def tagged (tag : String) (v : Json) : Json :=
  Json.mkObj [(tag, v)]

/-! ### Accounts, keys, validators -/

def validatorStakeView (v : ValidatorStake) : Json :=
  Json.mkObj
    [("validator_stake_struct_version", "V1"), ("account_id", jacc v.accountId),
      ("public_key", jkey v.publicKey), ("stake", jbal v.stake)]

def permissionView : AccessKeyPermission → Json
  | .functionCall p =>
    tagged "FunctionCall"
      (Json.mkObj
        [("allowance", jopt jbal p.allowance), ("receiver_id", p.receiverId),
          ("method_names", jarr Json.str p.methodNames)])
  | .fullAccess => Json.str "FullAccess"
  | .gasKeyFunctionCall i p =>
    tagged "GasKeyFunctionCall"
      (Json.mkObj
        [("balance", jbal i.balance), ("num_nonces", jn i.numNonces.toNat),
          ("allowance", jopt jbal p.allowance), ("receiver_id", p.receiverId),
          ("method_names", jarr Json.str p.methodNames)])
  | .gasKeyFullAccess i =>
    tagged "GasKeyFullAccess"
      (Json.mkObj [("balance", jbal i.balance), ("num_nonces", jn i.numNonces.toNat)])

def accessKeyView (k : AccessKey) : Json :=
  Json.mkObj [("nonce", jn k.nonce.toNat), ("permission", permissionView k.permission)]

/-! ### Actions -/

private def globalIdView : GlobalContractIdentifier → Json
  | .codeHash h => Json.mkObj [("hash", jhash h)]
  | .accountId a => Json.mkObj [("account_id", jacc a)]

/-- `ActionView` of a base action. `raw` writes the code of a deployment in full instead of its hash
(the `NonDelegateAction` inside a delegate action is serialized as the `Action` itself). -/
def baseActionView (raw : Bool) : BaseAction → Json
  | .createAccount => Json.str "CreateAccount"
  | .deployContract a =>
    tagged "DeployContract"
      (Json.mkObj [("code", jbytes (if raw then a.code else (CryptoHash.hash a.code).bytes))])
  | .functionCall a =>
    tagged "FunctionCall"
      (Json.mkObj
        [("method_name", a.methodName), ("args", jbytes a.args), ("gas", jn a.gas.toNat),
          ("deposit", jbal a.deposit)])
  | .transfer a => tagged "Transfer" (Json.mkObj [("deposit", jbal a.deposit)])
  | .stake a =>
    tagged "Stake" (Json.mkObj [("stake", jbal a.stake), ("public_key", jkey a.publicKey)])
  | .addKey a =>
    tagged "AddKey"
      (Json.mkObj [("public_key", jkey a.publicKey), ("access_key", accessKeyView a.accessKey)])
  | .deleteKey a => tagged "DeleteKey" (Json.mkObj [("public_key", jkey a.publicKey)])
  | .deleteAccount a =>
    tagged "DeleteAccount" (Json.mkObj [("beneficiary_id", jacc a.beneficiaryId)])
  | .deployGlobalContract a =>
    let code :=
      Json.mkObj [("code", jbytes (if raw then a.code else (CryptoHash.hash a.code).bytes))]
    match a.deployMode with
    | .codeHash => tagged "DeployGlobalContract" code
    | .accountId => tagged "DeployGlobalContractByAccountId" code
  | .useGlobalContract a =>
    match a.contractIdentifier with
    | .codeHash h => tagged "UseGlobalContract" (Json.mkObj [("code_hash", jhash h)])
    | .accountId id => tagged "UseGlobalContractByAccountId" (Json.mkObj [("account_id", jacc id)])
  | .deterministicStateInit _ => tagged "DeterministicStateInit" Json.null
  | .transferToGasKey a =>
    tagged "TransferToGasKey"
      (Json.mkObj [("public_key", jkey a.publicKey), ("deposit", jbal a.deposit)])
  | .withdrawFromGasKey a =>
    tagged "WithdrawFromGasKey"
      (Json.mkObj [("public_key", jkey a.publicKey), ("amount", jbal a.amount)])

private def delegateActionJson (d : DelegateAction) : Json :=
  Json.mkObj
    [("sender_id", jacc d.senderId), ("receiver_id", jacc d.receiverId),
      ("actions", jarr (baseActionView true) d.actions), ("nonce", jn d.nonce.toNat),
      ("max_block_height", jn d.maxBlockHeight.toNat), ("public_key", jkey d.publicKey)]

def actionView : Action → Json
  | .base a => baseActionView false a
  | .delegate a =>
    tagged "Delegate"
      (Json.mkObj
        [("delegate_action", delegateActionJson a.delegateAction), ("signature", jsig a.signature)])
  | .delegateV2 a =>
    tagged "DelegateV2"
      (Json.mkObj [("delegate_action", Json.null), ("signature", jsig a.signature)])

/-! ### Transactions -/

def signedTransactionView (t : SignedTransaction) : Json :=
  let tx := t.transaction
  let base : List (String × Json) :=
    [("signer_id", jacc tx.signerId), ("public_key", jkey tx.publicKey),
      ("nonce", jn tx.nonceValue.toNat), ("receiver_id", jacc tx.receiverId),
      ("actions", jarr actionView tx.actions), ("priority_fee", jn 0),
      ("signature", jsig t.signature), ("hash", jhash t.hash)]
  let extra : List (String × Json) :=
    (match tx.nonceIndex with
      | some i => [("nonce_index", jn i.toNat)]
      | none => []) ++
      (if tx.isStrict then [("nonce_mode", Json.str "strict")] else [])
  Json.mkObj (base ++ extra)

/-! ### Receipts -/

private def actionReceiptView (r : ActionReceipt) (refundTo : Option AccountId) (yield : Bool) :
    Json :=
  let base : List (String × Json) :=
    [("signer_id", jacc r.signerId), ("signer_public_key", jkey r.signerPublicKey),
      ("gas_price", jbal r.gasPrice),
      ("output_data_receivers",
        jarr
          (fun (d : DataReceiver) =>
            Json.mkObj [("data_id", jhash d.dataId), ("receiver_id", jacc d.receiverId)])
          r.outputDataReceivers),
      ("input_data_ids", jarr jhash r.inputDataIds), ("actions", jarr actionView r.actions),
      ("is_promise_yield", Json.bool yield)]
  tagged "Action"
    (Json.mkObj
      (base ++
        (match refundTo with
        | some a => [("refund_to", jacc a)]
        | none => [])))

private def dataReceiptView (r : DataReceipt) (resume : Bool) : Json :=
  tagged "Data"
    (Json.mkObj
      [("data_id", jhash r.dataId), ("data", jopt jbytes r.data),
        ("is_promise_resume", Json.bool resume)])

def receiptView : Receipt → Json
  | .v0 r =>
    let body : Json :=
      match r.receipt with
      | .action a => actionReceiptView a none false
      | .promiseYield a => actionReceiptView a none true
      | .actionV2 a =>
        actionReceiptView
          { signerId := a.signerId, signerPublicKey := a.signerPublicKey, gasPrice := a.gasPrice,
            outputDataReceivers := a.outputDataReceivers, inputDataIds := a.inputDataIds,
            actions := a.actions }
          a.refundTo false
      | .promiseYieldV2 a =>
        actionReceiptView
          { signerId := a.signerId, signerPublicKey := a.signerPublicKey, gasPrice := a.gasPrice,
            outputDataReceivers := a.outputDataReceivers, inputDataIds := a.inputDataIds,
            actions := a.actions }
          a.refundTo true
      | .data d => dataReceiptView d false
      | .promiseResume d => dataReceiptView d true
      | .globalContractDistribution _ => tagged "GlobalContractDistribution" Json.null
    Json.mkObj
      [("predecessor_id", jacc r.predecessorId), ("receiver_id", jacc r.receiverId),
        ("receipt_id", jhash r.receiptId), ("receipt", body), ("priority", jn 0)]

/-! ### Execution outcomes -/

def merklePathView (p : Array MerklePathItem) : Json :=
  jarr
    (fun (i : MerklePathItem) =>
      Json.mkObj
        [("hash", jhash i.hash),
          ("direction",
            Json.str
              (match i.direction with
              | .left => "Left"
              | .right => "Right"))])
    p

def outcomeView (o : ExecutionOutcome) : Json :=
  let status : Json :=
    match o.status with
    | .unknown => Json.str "Unknown"
    | .failure _ => tagged "Failure" Json.null
    | .successValue v => tagged "SuccessValue" (jbytes v)
    | .successReceiptId r => tagged "SuccessReceiptId" (jhash r)
  Json.mkObj
    [("logs", jarr Json.str o.logs), ("receipt_ids", jarr jhash o.receiptIds),
      ("gas_burnt", jn o.gasBurnt.toNat), ("tokens_burnt", jbal o.tokensBurnt),
      ("executor_id", jacc o.executorId), ("status", status),
      ("metadata", Json.mkObj [("version", jn 1), ("gas_profile", Json.null)])]

end Near.Node.Rpc
