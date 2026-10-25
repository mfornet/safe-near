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
      | .globalContractDistribution d =>
        -- `ReceiptEnumView::GlobalContractDistribution`: the code appears as its hash, the nonce only in version 2
        let view (id : GlobalContractIdentifier) (target : ShardId) (delivered : Array ShardId)
          (code : ByteArray) (nonce : Option UInt64) : Json :=
          tagged "GlobalContractDistribution"
            (Json.mkObj
              ([("id", globalIdView id), ("target_shard", jn target.toNat),
                  ("already_delivered_shards", jarr (fun (s : ShardId) => jn s.toNat) delivered),
                  ("code", jbytes (CryptoHash.hash code).bytes)] ++
                match nonce with
                | some n => [("nonce", jn n.toNat)]
                | none => []))
        match d with
        | .v1 r => view r.id r.targetShard r.alreadyDeliveredShards r.code none
        | .v2 r => view r.id r.targetShard r.alreadyDeliveredShards r.code (some r.nonce)
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

/-- The `ActionErrorKind` as nearcore's `serde` renders it. -/
def actionErrorKindJson : ActionErrorKind → Json
  | .accountAlreadyExists a => tagged "AccountAlreadyExists" (Json.mkObj [("account_id", jacc a)])
  | .accountDoesNotExist a => tagged "AccountDoesNotExist" (Json.mkObj [("account_id", jacc a)])
  | .createAccountOnlyByRegistrar a r p =>
    tagged "CreateAccountOnlyByRegistrar"
      (Json.mkObj
        [("account_id", jacc a), ("registrar_account_id", jacc r), ("predecessor_id", jacc p)])
  | .createAccountNotAllowed a p =>
    tagged "CreateAccountNotAllowed"
      (Json.mkObj [("account_id", jacc a), ("predecessor_id", jacc p)])
  | .actorNoPermission a x =>
    tagged "ActorNoPermission" (Json.mkObj [("account_id", jacc a), ("actor_id", jacc x)])
  | .deleteKeyDoesNotExist a k =>
    tagged "DeleteKeyDoesNotExist" (Json.mkObj [("account_id", jacc a), ("public_key", jkey k)])
  | .addKeyAlreadyExists a k =>
    tagged "AddKeyAlreadyExists" (Json.mkObj [("account_id", jacc a), ("public_key", jkey k)])
  | .deleteAccountStaking a => tagged "DeleteAccountStaking" (Json.mkObj [("account_id", jacc a)])
  | .lackBalanceForState a n =>
    tagged "LackBalanceForState" (Json.mkObj [("account_id", jacc a), ("amount", jbal n)])
  | .triesToUnstake a => tagged "TriesToUnstake" (Json.mkObj [("account_id", jacc a)])
  | .triesToStake a s l b =>
    tagged "TriesToStake"
      (Json.mkObj
        [("account_id", jacc a), ("stake", jbal s), ("locked", jbal l), ("balance", jbal b)])
  | .insufficientStake a s m =>
    tagged "InsufficientStake"
      (Json.mkObj [("account_id", jacc a), ("stake", jbal s), ("minimum_stake", jbal m)])
  | .functionCallError (.executionError m) =>
    tagged "FunctionCallError" (tagged "ExecutionError" (Json.str m))
  | .functionCallError (.methodResolveError m) =>
    tagged "FunctionCallError"
      (tagged "MethodResolveError"
        (Json.str
          (match m with
          | .methodEmptyName => "MethodEmptyName"
          | .methodNotFound => "MethodNotFound"
          | .methodInvalidSignature => "MethodInvalidSignature")))
  | .deleteAccountWithLargeState a =>
    tagged "DeleteAccountWithLargeState" (Json.mkObj [("account_id", jacc a)])
  | .onlyImplicitAccountCreationAllowed a =>
    tagged "OnlyImplicitAccountCreationAllowed" (Json.mkObj [("account_id", jacc a)])
  | .delegateActionInvalidSignature => Json.str "DelegateActionInvalidSignature"
  | .delegateActionSenderDoesNotMatchTxReceiver s r =>
    tagged "DelegateActionSenderDoesNotMatchTxReceiver"
      (Json.mkObj [("sender_id", jacc s), ("receiver_id", jacc r)])
  | .delegateActionExpired => Json.str "DelegateActionExpired"
  | .delegateActionInvalidNonce d a =>
    tagged "DelegateActionInvalidNonce"
      (Json.mkObj [("delegate_nonce", jn d.toNat), ("ak_nonce", jn a.toNat)])
  | .delegateActionNonceTooLarge d u =>
    tagged "DelegateActionNonceTooLarge"
      (Json.mkObj [("delegate_nonce", jn d.toNat), ("upper_bound", jn u.toNat)])
  | _ => Json.str "<unrendered action error>"

/-- The failure of an outcome. The kinds `actionErrorKindJson` does not render, and the errors the node does not
tell apart (`placeholderFailure`), are the string `<unrendered failure>`; the conformance run counts them. -/
def failureView : TxExecutionError → Json
  | .actionError ⟨some i, k⟩ =>
    match k with
    | .functionCallError (.executionError m) =>
      if m == "the failure is not detailed by the node" then Json.str "<unrendered failure>"
      else
        tagged "ActionError" (Json.mkObj [("index", jn i.toNat), ("kind", actionErrorKindJson k)])
    | _ =>
      tagged "ActionError" (Json.mkObj [("index", jn i.toNat), ("kind", actionErrorKindJson k)])
  | _ => Json.str "<unrendered failure>"

def outcomeView (o : ExecutionOutcome) (version : Nat := 1) : Json :=
  let status : Json :=
    match o.status with
    | .unknown => Json.str "Unknown"
    | .failure e => tagged "Failure" (failureView e)
    | .successValue v => tagged "SuccessValue" (jbytes v)
    | .successReceiptId r => tagged "SuccessReceiptId" (jhash r)
  Json.mkObj
    [("logs", jarr Json.str o.logs), ("receipt_ids", jarr jhash o.receiptIds),
      ("gas_burnt", jn o.gasBurnt.toNat), ("tokens_burnt", jbal o.tokensBurnt),
      ("executor_id", jacc o.executorId), ("status", status),
      ("metadata",
        Json.mkObj
          [("version", jn version), ("gas_profile", Json.arr #[]), ("contracts", Json.arr #[])])]

end Near.Node.Rpc
