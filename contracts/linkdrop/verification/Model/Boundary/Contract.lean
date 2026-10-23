import Model.Boundary.State
import Model.Boundary.Metadata
import NearVM.PromiseGas
import NearInterface.Model

/-!
# linkdrop at the function-call boundary

The contract of `src/lib.rs` (near-linkdrop 9a6bb316, near-sdk 5.17.1) as
the binary behaves, observed on `contract.wasm` through near-lean:

* the SDK wrapper checks, in order: `#[private]` (predecessor is the contract),
  no deposit for methods that are neither `#[payable]` nor views, argument
  decoding, then the state (`new` instead checks that there is none and never
  reads its input);
* panic messages are exact: `assert!` and `expect` carry their source location;
* the signer key and the callback result are read where the source reads
  them; an unparsable signer key or a not-ready result traps (`unreachable`);
* promises become receipts in the order the SDK schedules them; the callbacks
  attach 13 Tgas with weight 1, so they also receive the unused gas.

The method semantics mirror `Model/Methods.lean` on abstract keys.
-/

namespace Linkdrop.Boundary

open NearInterface (Context RawStorage storageUsageOf stakeDeficit receiptDeposits)
open NearInterface.Json
open Wasm.Near (ReturnData ReceiptSpec)

abbrev AccountId := NearInterface.AccountId

/-! ## Calls -/

structure LimitedKey where
  key : PublicKey
  allowance : Nat
  receiver : AccountId
  methods : String

structure Options where
  fullKeys : Option (List PublicKey) := none
  limitedKeys : Option (List LimitedKey) := none
  bytes : Option Bytes := none
  base64Bytes : Option Bytes := none
  globalHash : Option Bytes := none
  globalAccount : Option AccountId := none

inductive Call where
  | new
  | send (key : PublicKey)
  | claim (account : AccountId)
  | createAndClaim (account : AccountId) (key : PublicKey)
  | createAccount (account : AccountId) (key : PublicKey)
  | createAdvanced (account : AccountId) (options : Options)
  | onCreated (predecessor : AccountId) (amount : Nat)
  | onClaimed (amount : Nat)
  | getBalance (key : PublicKey)
  | getInformation (key : PublicKey)
  /-- `contract_source_metadata`, added by `cargo near`. -/
  | sourceMetadata
  /-- `__contract_abi`, added by `cargo near`. -/
  | abi

def Call.method : Call → String
  | .new => "new"
  | .send _ => "send"
  | .claim _ => "claim"
  | .createAndClaim .. => "create_account_and_claim"
  | .createAccount .. => "create_account"
  | .createAdvanced .. => "create_account_advanced"
  | .onCreated .. => "on_account_created"
  | .onClaimed _ => "on_account_created_and_claimed"
  | .getBalance _ => "get_key_balance"
  | .getInformation _ => "get_key_information"
  | .sourceMetadata => "contract_source_metadata"
  | .abi => "__contract_abi"

def Call.private : Call → Bool
  | .claim _ | .createAndClaim .. | .onCreated .. | .onClaimed _ => true
  | _ => false

def Call.payable : Call → Bool
  | .send _ | .createAccount .. | .createAdvanced .. => true
  | _ => false

/-- `&self` methods: no deposit check, no state write. -/
def Call.view : Call → Bool
  | .getBalance _ | .getInformation _ => true
  | _ => false

/-! ## Which inputs are calls

`#[near]` reads a method's arguments with `serde_json::from_slice` into a
struct with one field per parameter (`NearInterface.Json.structFields`). -/

def limitedKey (v : Value) : Option LimitedKey := do
  let fs ← structFields ["public_key", "allowance", "receiver_id", "method_names"] v
  let key ← required publicKey fs[0]?.join
  let allowance ← required token fs[1]?.join
  let receiver ← required accountId fs[2]?.join
  let methods ← required string fs[3]?.join
  pure { key, allowance, receiver, methods }

def options (v : Value) : Option Options := do
  let fs ← structFields ["full_access_keys", "limited_access_keys", "contract_bytes",
    "contract_bytes_base64", "use_global_contract_hash", "use_global_contract_account_id"] v
  let fullKeys ← optional (array publicKey) fs[0]?.join
  let limitedKeys ← optional (array limitedKey) fs[1]?.join
  let bytes ← optional (array byte) fs[2]?.join
  let base64Bytes ← optional base64Bytes fs[3]?.join
  let globalHash ← optional cryptoHash fs[4]?.join
  let globalAccount ← optional accountId fs[5]?.join
  pure { fullKeys, limitedKeys, bytes, base64Bytes, globalHash, globalAccount }

def Call.decode (method : String) (args : Bytes) : Option Call :=
  let fields (names : List String) := (parse args).bind (structFields names)
  match method with
  | "new" => some .new
  | "contract_source_metadata" => some .sourceMetadata
  | "__contract_abi" => some .abi
  | "send" => do
    let fs ← fields ["public_key"]
    pure (.send (← required publicKey fs[0]?.join))
  | "claim" => do
    let fs ← fields ["account_id"]
    pure (.claim (← required accountId fs[0]?.join))
  | "create_account_and_claim" => do
    let fs ← fields ["new_account_id", "new_public_key"]
    pure (.createAndClaim (← required accountId fs[0]?.join) (← required publicKey fs[1]?.join))
  | "create_account" => do
    let fs ← fields ["new_account_id", "new_public_key"]
    pure (.createAccount (← required accountId fs[0]?.join) (← required publicKey fs[1]?.join))
  | "create_account_advanced" => do
    let fs ← fields ["new_account_id", "options"]
    pure (.createAdvanced (← required accountId fs[0]?.join) (← required options fs[1]?.join))
  | "on_account_created" => do
    let fs ← fields ["predecessor_account_id", "amount"]
    pure (.onCreated (← required accountId fs[0]?.join) (← required token fs[1]?.join))
  | "on_account_created_and_claimed" => do
    let fs ← fields ["amount"]
    pure (.onClaimed (← required token fs[0]?.join))
  | "get_key_balance" => do
    let fs ← fields ["key"]
    pure (.getBalance (← required publicKey fs[0]?.join))
  | "get_key_information" => do
    let fs ← fields ["key"]
    pure (.getInformation (← required publicKey fs[0]?.join))
  | _ => none

def Parses (method : String) (args : Bytes) (c : Call) : Prop := Call.decode method args = some c

theorem Parses.functional {method : String} {args : Bytes} {c c' : Call}
    (h : Parses method args c) (h' : Parses method args c') : c = c' :=
  Option.some.inj (h.symm.trans h')

/-! ## The environment of one call -/

structure Env where
  current : AccountId
  predecessor : AccountId
  deposit : Nat
  /-- `env::signer_account_pk()`; `none` if its bytes are no SDK `PublicKey`. -/
  signerKey : Option PublicKey
  results : List Wasm.PromiseResult

def Env.ofContext (ctx : Context) : Env where
  current := ctx.current
  predecessor := ctx.predecessor
  deposit := ctx.attached
  signerKey := PublicKey.ofData? ctx.signerPk
  results := ctx.promiseResults

/-! ## Panics -/

inductive Panic where
  | initialized
  | uninitialized
  | deposit (method : String)
  | privateCall (method : String)
  | zeroDeposit
  | claimMissing
  | createAndClaimMissing
  | balanceMissing
  | informationMissing
  | noOptions
  | conflictingOptions
  | resultCount
  /-- `unreachable`: an unparsable signer key or a not-ready callback result. -/
  | trap

def Panic.message : Panic → String
  | .initialized => "The contract has already been initialized"
  | .uninitialized => "The contract is not initialized"
  | .deposit m => s!"Method {m} doesn't accept deposit"
  | .privateCall m => s!"Method {m} is private"
  | .zeroDeposit => "panicked at src/lib.rs:42:9:\nAttached deposit must be at least 1 yoctoNEAR"
  | .claimMissing => "panicked at src/lib.rs:69:14:\nUnexpected public key"
  | .createAndClaimMissing => "panicked at src/lib.rs:87:14:\nUnexpected public key"
  | .balanceMissing => "panicked at src/lib.rs:242:33:\nKey is missing"
  | .informationMissing => "Key is missing"
  | .noOptions => "panicked at src/lib.rs:131:9:\nCannot create account with no options. " ++
      "Please specify either contract bytes, full access keys, limited access keys, or global contract options."
  | .conflictingOptions => "panicked at src/lib.rs:147:9:\nCannot specify multiple contract deployment " ++
      "options. Choose only one: contract_bytes, contract_bytes_base64, use_global_contract_hash, or " ++
      "use_global_contract_account_id."
  | .resultCount => "Contract expected a single result on the callback"
  | .trap => "WebAssembly trap: An `unreachable` opcode was executed."

def Panic.failure : Panic → NearInterface.Failure
  | .trap => .other Panic.trap.message
  | p => .panic p.message

/-! ## Receipts -/

/-- A `u128`/`NearToken` as serde_json writes it: a JSON string. -/
def jsonU128 (n : Nat) : String := quote (toString n)

/-- Gas the callbacks attach (`ON_CREATE_ACCOUNT_CALLBACK_GAS`). -/
def callbackGas : Nat := 13 * 10 ^ 12

/-- Allowance of the keys `send` adds (`ACCESS_KEY_ALLOWANCE`). -/
def keyAllowance : Nat := 10 ^ 24

def keyMethods : String := "claim,create_account_and_claim"

inductive Action where
  | create
  | transfer (amount : Nat)
  | fullKey (key : PublicKey)
  /-- `none` is an unlimited allowance (`0` in the arguments). -/
  | limitedKey (key : PublicKey) (allowance : Option Nat) (receiver : AccountId) (methods : String)
  | deleteKey (key : PublicKey)
  | deploy (code : Bytes)
  | globalHash (hash : Bytes)
  | globalAccount (account : AccountId)
  /-- `on_account_created(predecessor, amount)`: 13 Tgas, weight 1. -/
  | onCreated (predecessor : AccountId) (amount : Nat)
  /-- `on_account_created_and_claimed(amount)`: 13 Tgas, weight 1. -/
  | onClaimed (amount : Nat)

structure Receipt where
  receiver : AccountId
  actions : List Action
  /-- Scheduled with `.then` on the previous receipt. -/
  afterPrevious : Bool := false

def Action.weighted : Action → Bool
  | .onCreated .. | .onClaimed _ => true
  | _ => false

/-- The method and JSON arguments of a callback. -/
def callbackCall : Action → String × String
  | .onCreated predecessor amount =>
    ("on_account_created",
      "{\"predecessor_account_id\":" ++ quote predecessor.val ++ ",\"amount\":" ++ jsonU128 amount ++ "}")
  | .onClaimed amount => ("on_account_created_and_claimed", "{\"amount\":" ++ jsonU128 amount ++ "}")
  | _ => ("", "")

/-- The share of the leftover gas the `i`-th of `n` weighted calls receives
(`distribute_gas`, every weight 1). -/
def share (leftover n i : Nat) : Nat :=
  leftover / n + (if i + 1 = n then leftover - n * (leftover / n) else 0)

def Action.encode (leftover n : Nat) (i : Nat) : Action → Wasm.PromiseAction
  | .create => .createAccount
  | .transfer amount => .transfer amount
  | .fullKey key => .addKey key.val 0 .fullAccess
  | .limitedKey key allowance receiver methods =>
    .addKey key.val 0 (.functionCall allowance receiver.bytes methods.toUTF8.toList)
  | .deleteKey key => .deleteKey key.val
  | .deploy code => .deployContract code
  | .globalHash hash => .useGlobalContract (.codeHash hash)
  | .globalAccount account => .useGlobalContract (.accountId account.bytes)
  | a@(.onCreated ..) | a@(.onClaimed _) =>
    let (method, args) := callbackCall a
    .functionCall method.toUTF8.toList args.toUTF8.toList 0 (UInt64.ofNat (callbackGas + share leftover n i))

/-- Encode actions, numbering the weighted ones from `i`. -/
def encodeActions (leftover n : Nat) : Nat → List Action → List Wasm.PromiseAction
  | _, [] => []
  | i, a :: rest =>
    a.encode leftover n i :: encodeActions leftover n (if a.weighted then i + 1 else i) rest

def encodeReceiptsFrom (leftover n : Nat) : Nat → Nat → List Receipt → List ReceiptSpec
  | _, _, [] => []
  | index, i, r :: rest =>
    { receiverId := r.receiver.bytes, actions := encodeActions leftover n i r.actions
      dependencies := if r.afterPrevious then [index - 1] else [] } ::
    encodeReceiptsFrom leftover n (index + 1) (i + (r.actions.filter Action.weighted).length) rest

/-- The receipts of a call, the leftover gas `prepaid - used` shared among
the weighted calls. -/
def encodeReceipts (leftover : Nat) (receipts : List Receipt) : List ReceiptSpec :=
  encodeReceiptsFrom leftover (receipts.flatMap (·.actions) |>.filter Action.weighted).length 0 0 receipts

/-! ## Return values -/

inductive Ret where
  | unit
  | bool (b : Bool)
  | balance (amount : Nat)
  | information (amount : Nat)
  | promise (index : Nat)
  | bytes (value : Bytes)

def encodeRet : Ret → ReturnData
  | .unit => .none
  | .promise index => .receiptIndex index
  | .bool b => .value (toString b).toUTF8.toList
  | .balance n => .value (jsonU128 n).toUTF8.toList
  | .information n => .value ("{\"balance\":" ++ jsonU128 n ++ "}").toUTF8.toList
  | .bytes value => .value value

/-! ## Methods -/

abbrev Result := Except Panic (Map × Ret × List Receipt)

def Options.present (o : Options) : Bool :=
  o.fullKeys.isSome || o.limitedKeys.isSome || o.bytes.isSome || o.base64Bytes.isSome ||
    o.globalHash.isSome || o.globalAccount.isSome

def Options.deployments (o : Options) : Nat :=
  o.bytes.isSome.toNat + o.base64Bytes.isSome.toNat + o.globalHash.isSome.toNat +
    o.globalAccount.isSome.toNat

def Options.actions (o : Options) : List Action :=
  (o.fullKeys.getD []).map .fullKey ++
  (o.limitedKeys.getD []).map (fun k =>
    .limitedKey k.key (if k.allowance = 0 then none else some k.allowance) k.receiver k.methods) ++
  o.bytes.toList.map .deploy ++ o.base64Bytes.toList.map .deploy ++
  o.globalHash.toList.map .globalHash ++ o.globalAccount.toList.map .globalAccount

/-- `is_promise_success()`: exactly one result, which must be ready. -/
def promiseSuccess (e : Env) : Except Panic Bool :=
  match e.results with
  | [.successful _] => .ok true
  | [.failed] => .ok false
  | [.notReady] => .error .trap
  | _ => .error .resultCount

def signer (e : Env) : Except Panic PublicKey :=
  match e.signerKey with
  | some k => .ok k
  | none => .error .trap

def body (s : Map) (e : Env) : Call → Result
  | .new => .ok (⟨[]⟩, .unit, [])
  | .send key =>
    if e.deposit = 0 then .error .zeroDeposit else
    .ok (s.insert key (min ((s.get key).getD 0 + e.deposit) maxAmount), .promise 0,
      [{ receiver := e.current, actions := [.limitedKey key (some keyAllowance) e.current keyMethods] }])
  | .claim account => do
    let k ← signer e
    let some amount := s.get k | .error .claimMissing
    pure (s.remove k, .promise 1,
      [{ receiver := e.current, actions := [.deleteKey k] },
       { receiver := account, actions := [.transfer amount] }])
  | .createAndClaim account key => do
    let k ← signer e
    let some amount := s.get k | .error .createAndClaimMissing
    pure (s.remove k, .promise 1,
      [{ receiver := account, actions := [.create, .fullKey key, .transfer amount] },
       { receiver := e.current, actions := [.onClaimed amount], afterPrevious := true }])
  | .createAccount account key =>
    .ok (s, .promise 1,
      [{ receiver := account, actions := [.create, .fullKey key, .transfer e.deposit] },
       { receiver := e.current, actions := [.onCreated e.predecessor e.deposit], afterPrevious := true }])
  | .createAdvanced account o =>
    if !o.present then .error .noOptions else
    if o.deployments > 1 then .error .conflictingOptions else
    .ok (s, .promise 1,
      [{ receiver := account, actions := [.create, .transfer e.deposit] ++ o.actions },
       { receiver := e.current, actions := [.onCreated e.predecessor e.deposit], afterPrevious := true }])
  | .onCreated predecessor amount => do
    let success ← promiseSuccess e
    pure (s, .bool success,
      if success then [] else [{ receiver := predecessor, actions := [.transfer amount] }])
  | .onClaimed amount => do
    let success ← promiseSuccess e
    let k ← signer e
    if success then pure (s, .bool true, [{ receiver := e.current, actions := [.deleteKey k] }])
    else pure (s.insert k amount, .bool false, [])
  | .getBalance key =>
    match s.get key with
    | some n => .ok (s, .balance n, [])
    | none => .error .balanceMissing
  | .getInformation key =>
    match s.get key with
    | some n => .ok (s, .information n, [])
    | none => .error .informationMissing
  | .sourceMetadata | .abi => .ok (s, .unit, [])

/-- The metadata exports, then the SDK wrapper's checks, then the method. -/
def step (e : Env) (st : State) (c : Call) : Except Panic (State × Ret × List Receipt) :=
  match c with
  | .sourceMetadata => .ok (st, .bytes sourceMetadata.toUTF8.toList, [])
  | .abi => .ok (st, .bytes abiBytes, [])
  | c =>
    if c.private && e.predecessor != e.current then .error (.privateCall c.method) else
    if !c.payable && !c.view && e.deposit != 0 then .error (.deposit c.method) else
    match c, st with
    | .new, some _ => .error .initialized
    | .new, none => (body ⟨[]⟩ e .new).map fun (m, r, rs) => (some m, r, rs)
    | _, none => .error .uninitialized
    | c, some s => (body s e c).map fun (m, r, rs) => (some m, r, rs)

/-! ## One call at the boundary -/

/-- The model's states are `Option State`; an uninitialised `none` and an empty
`some none` are the same empty storage. -/
def flat (st : Option State) : State := st.bind id

def storageOf (st : Option State) : RawStorage := encode (flat st)

def usageAfter (ctx : Context) (st : Option State) (s' : State) : Nat :=
  ctx.storageUsage - storageUsageOf ctx.protocol (storageOf st) +
    storageUsageOf ctx.protocol (encode s')

abbrev StepResult := NearInterface.StepResult Panic State Ret Receipt

/-- `step` on the context, then the runtime's checks on a success: the
transfers against the liquid balance, and the storage stake. -/
def contractStep (ctx : Context) (st : Option State) (c : Call) : StepResult :=
  match step (Env.ofContext ctx) (flat st) c with
  | .error p => .error { failure := .panic p, logs := [] }
  | .ok (s', ret, receipts) =>
    let available := ctx.balance + ctx.attached
    let out := receiptDeposits (encodeReceipts 0 receipts)
    if available < out then .error { failure := .balanceExceeded, logs := [] }
    else
      let deficit := stakeDeficit ctx.protocol (usageAfter ctx st s') (available - out) ctx.locked
      if 0 < deficit then .error { failure := .lackBalanceForState deficit, logs := [] }
      else .ok { state := s', ret, logs := [], promises := receipts }

/-! ## Gas

`gasBound` bounds the VM's used gas (before distribution): the gas burnt, plus
the execution fees and static gas of the receipts the call creates. Compute
and argument decoding are measured on `contract.wasm`; storage pays every node
of the longest trie path cold for each distinct key and cached for each
access. -/

/-- Sending plus executing a fee, whatever the receiver. -/
def Fee.bound (f : Wasm.Near.Fee) : Nat := max f.sendSir f.sendNotSir + f.execution

def actionGasBound (ctx : Context) (receiver : AccountId) (a : Wasm.PromiseAction) : Nat :=
  let f := ctx.protocol.fees.actionFees
  match a with
  | .createAccount => Fee.bound f.createAccount
  | .deployContract code => Fee.bound f.deployContractBase + Fee.bound f.deployContractByte * code.length
  | .functionCall method args _ gas =>
    Fee.bound f.functionCallBase + Fee.bound f.functionCallByte * (method.length + args.length) + gas.toNat
  | .transfer _ => Fee.bound (Wasm.Near.transferFees f ctx.protocol.wasm.ethImplicitAccounts receiver.bytes)
  | .stake .. => Fee.bound f.stake
  | .addKey _ _ .fullAccess => Fee.bound f.addFullAccessKey
  | .addKey _ _ (.functionCall _ _ methods) =>
    Fee.bound f.addFunctionCallKeyBase + Fee.bound f.addFunctionCallKeyByte * methods.length
  | .deleteKey _ => Fee.bound f.deleteKey
  | .deleteAccount _ => Fee.bound f.deleteAccount
  | .useGlobalContract id => Fee.bound f.useGlobalContractBase + Fee.bound f.useGlobalContractByte * id.length

def receiptGasBound (ctx : Context) (r : Receipt) : Nat :=
  let f := ctx.protocol.fees.actionFees
  Fee.bound f.newActionReceipt + (if r.afterPrevious then Fee.bound f.newDataReceiptBase else 0) +
    ((encodeActions 0 1 0 r.actions).map (actionGasBound ctx r.receiver)).sum

/-- Wasm execution and host calls other than storage, with short arguments. -/
def computeGas : Nat := 5 * 10 ^ 12
/-- Per byte of the arguments. -/
def argumentByteGas : Nat := 400 * 10 ^ 6
/-- Longest contract key: `ai` and a Borsh secp256k1 key. -/
def maxStorageKeyBytes : Nat := 2 + 4 + 65
/-- Distinct storage keys a call touches: `STATE`, an entry and the last entry. -/
def storageKeysTouched : Nat := 7
/-- Storage host calls a call makes. -/
def storageAccesses : Nat := 16

def trieNodes (ctx : Context) : Nat := 2 * (2 + ctx.current.bytes.length + maxStorageKeyBytes) + 1

def trieGas (ctx : Context) : Nat :=
  let costs := ctx.protocol.wasm.extCosts
  storageKeysTouched * trieNodes ctx * costs.cost "touching_trie_node" +
    storageAccesses * trieNodes ctx * costs.cost "read_cached_trie_node"

def gasBound (ctx : Context) (st : Option State) (c : Call) : Nat :=
  let receipts := match step (Env.ofContext ctx) (flat st) c with
    | .ok (_, _, receipts) => receipts
    | .error _ => []
  (receipts.map (receiptGasBound ctx)).sum + computeGas + argumentByteGas * ctx.args.length + trieGas ctx

end Linkdrop.Boundary
