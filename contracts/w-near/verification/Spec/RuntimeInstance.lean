import Spec.Refinement
import NearVM

/-!
# The `RuntimeInterface` instance for `near-lean`

`Spec/Refinement.lean` asked for a runtime; `near-lean/vm` provides one.
This file instantiates `RuntimeInterface` with `NearVM.run` and encodes the
model's typed calls and return values the way near-sdk 3.1.0 serialises them
(JSON arguments, JSON return values, Borsh state). With it,
`Refines (nearLean cfg) code cfg` is a concrete statement about the module
decoded from `contract.wasm` and the protocol parameters `cfg`.
-/

namespace WNear

open Borsh Wasm.Near

/-- Encode arbitrary memo and message strings, including quotes, control
characters and Unicode, using a real JSON encoder. -/
def jsonString (s : String) : String := (Lean.Json.str s).compress

/-- near-sdk's JSON encoding of each call's arguments. Options are omitted when absent. -/
def Call.jsonArgs : Call → String
  | .new | .nearDeposit | .ftTotalSupply | .ftMetadata | .storageBalanceBounds | .storageMinimumBalance => "{}"
  | .nearWithdraw amount => "{\"amount\":" ++ jsonString (toString amount) ++ "}"
  | .ftTransfer receiver amount memo =>
    "{\"receiver_id\":" ++ jsonString receiver.val ++ ",\"amount\":" ++ jsonString (toString amount)
      ++ (match memo with | some m => ",\"memo\":" ++ jsonString m | none => "") ++ "}"
  | .ftTransferCall receiver amount memo msg =>
    "{\"receiver_id\":" ++ jsonString receiver.val ++ ",\"amount\":" ++ jsonString (toString amount)
      ++ (match memo with | some m => ",\"memo\":" ++ jsonString m | none => "")
      ++ ",\"msg\":" ++ jsonString msg ++ "}"
  | .ftResolveTransfer sender receiver amount =>
    "{\"sender_id\":" ++ jsonString sender.val ++ ",\"receiver_id\":" ++ jsonString receiver.val
      ++ ",\"amount\":" ++ jsonString (toString amount) ++ "}"
  | .ftBalanceOf a | .storageBalanceOf a => "{\"account_id\":" ++ jsonString a.val ++ "}"
  | .storageDeposit account registrationOnly =>
    "{" ++ ",".intercalate ((match account with | some a => ["\"account_id\":" ++ jsonString a.val] | none => [])
      ++ (match registrationOnly with | some b => ["\"registration_only\":" ++ toString b] | none => [])) ++ "}"
  | .storageWithdraw amount =>
    "{" ++ (match amount with | some n => "\"amount\":" ++ jsonString (toString n) | none => "") ++ "}"
  | .storageUnregister force =>
    "{" ++ (match force with | some b => "\"force\":" ++ toString b | none => "") ++ "}"

/-- The host context of a call: `Env` plus the arguments. -/
structure Input where
  method : String
  args : String
  env : Env
  resources : ExecutionResources

def mkInput (resources : ExecutionResources) (env : Env) (call : Call) : Input :=
  { method := call.methodName, args := call.jsonArgs, env, resources }

/-- The promise results the callback sees, from the model's view of them.
A parsed `U128` is re-serialised; an unparsable value is an empty body. -/
def promiseResultsOf (env : Env) : List Wasm.PromiseResult :=
  match env.promiseResult with
  | none => []
  | some .notReady => [.notReady]
  | some .failed => [.failed]
  | some (.successful (some u)) => [.successful (jsonString (toString u)).toUTF8.toList]
  | some (.successful none) => [.successful []]

def toVMContext (i : Input) : VMContext :=
  { currentAccountId := i.env.currentAccount.val.toUTF8.toList
    signerAccountId := i.env.predecessor.val.toUTF8.toList
    signerAccountPk := []
    predecessorAccountId := i.env.predecessor.val.toUTF8.toList
    input := i.args.toUTF8.toList
    promiseResults := promiseResultsOf i.env
    attachedDeposit := i.env.attachedDeposit
    prepaidGas := i.env.prepaidGas
    accountBalance := i.resources.balance
    storageUsage := i.resources.storageUsage }

/-- The adapter passes chain resources through without inventing funding. -/
theorem toVMContext_resources (resources : ExecutionResources) (env : Env) (call : Call) :
    (toVMContext (mkInput resources env call)).accountBalance = resources.balance ∧
    (toVMContext (mkInput resources env call)).storageUsage = resources.storageUsage :=
  ⟨rfl, rfl⟩

/-- JSON of a return value as near-sdk's serde emits it. -/
def Ret.json : Ret → String
  | .unit => ""
  | .u128 n => jsonString (toString n)
  | .bool b => toString b
  | .storageBalance b =>
    "{\"total\":" ++ jsonString (toString b.total) ++ ",\"available\":" ++ jsonString (toString b.available) ++ "}"
  | .optStorageBalance none => "null"
  | .optStorageBalance (some b) => Ret.json (.storageBalance b)
  | .storageBalanceBounds b =>
    "{\"min\":" ++ jsonString (toString b.min) ++ ",\"max\":"
      ++ (match b.max with | some m => jsonString (toString m) | none => "null") ++ "}"
  | .metadata m =>
    "{\"spec\":" ++ jsonString m.spec ++ ",\"name\":" ++ jsonString m.name ++ ",\"symbol\":" ++ jsonString m.symbol
      ++ ",\"icon\":null,\"reference\":null,\"reference_hash\":null,\"decimals\":" ++ toString m.decimals ++ "}"
  | .promise => ""

def encodeRet : Ret → ReturnData
  | .unit => .value []
  | .promise => .promise
  | r => .value r.json.toUTF8.toList

def returnDataOf (o : VMOutcome) : ReturnData :=
  match o.returnData with
  | .value b => .value b
  | .receiptIndex _ => .promise
  | .none => .value []

/-- Invalid account bytes are a failed projection, never a substitute account. -/
def accountOfBytes? (b : List UInt8) : Option AccountId := do
  let s ← String.fromUTF8? ⟨b.toArray⟩
  if h : isValidAccountId s = true then some ⟨s, h⟩ else none

def stringOfBytes (b : List UInt8) : String := (String.fromUTF8? ⟨b.toArray⟩).getD ""

/-- Parse escaped string fields without assuming whitespace or field order. -/
def jsonField (json key : String) : Option String :=
  (do
    let object ← Lean.Json.parse json
    let value ← object.getObjVal? key
    value.getStr?).toOption

/-- A receipt's actions as the model's promise: a transfer, or one of the two
function calls the contract makes. -/
def promiseOfSpec (s : ReceiptSpec) : Option Promise :=
  match s.actions with
  | [.transfer amount] => do
    let receiver ← accountOfBytes? s.receiverId
    pure (.transfer receiver amount)
  | [.functionCall m args deposit gas] =>
    let json := stringOfBytes args
    let call : Option OutgoingCall :=
      match stringOfBytes m with
      | "ft_on_transfer" => do
        let sender ← jsonField json "sender_id"
        let amount ← (← jsonField json "amount").toNat?
        let msg ← jsonField json "msg"
        let sender ← accountOfBytes? sender.toUTF8.toList
        pure (.ftOnTransfer sender amount msg)
      | "ft_resolve_transfer" => do
        let sender ← jsonField json "sender_id"
        let receiver ← jsonField json "receiver_id"
        let amount ← (← jsonField json "amount").toNat?
        let sender ← accountOfBytes? sender.toUTF8.toList
        let receiver ← accountOfBytes? receiver.toUTF8.toList
        pure (.ftResolveTransfer sender receiver amount)
      | _ => none
    do
      let c ← call
      let receiver ← accountOfBytes? s.receiverId
      pure (.call receiver c deposit gas.toNat)
  | _ => none

/-- Project every receipt exactly once into the model's linear promise chains.
Unknown actions, invalid accounts, joins, branching, and invalid dependencies
fail the projection instead of disappearing from the observed promise list. -/
def promisesOf? (o : VMOutcome) : Option (List Promise) := do
  let mut chains : List (Nat × Promise) := []
  for (spec, i) in o.receipts.zipIdx do
    let promise ← promiseOfSpec spec
    match spec.dependencies with
    | [] => chains := chains ++ [(i, promise)]
    | [dep] =>
      let (_, previous) ← chains.find? (fun entry => entry.1 == dep)
      chains := chains.map fun (tip, tree) =>
        if tip == dep then (i, .then previous promise) else (tip, tree)
    | _ => none
  pure (chains.map (·.2))

def promisesOf (o : VMOutcome) : List Promise := (promisesOf? o).getD []

/-- The model has no arbitrary returned-receipt selector. wNEAR's returned
promise must be the last receipt of its sole chain. -/
def observationsValid (o : VMOutcome) : Bool :=
  (promisesOf? o).isSome &&
    match o.returnData with
    | .receiptIndex idx => idx + 1 == o.receipts.length &&
        ((promisesOf? o).map (fun ps => ps.length == 1)).getD false
    | _ => true

/-- The storage as the model sees it. -/
def rawOf (s : List (List UInt8 × List UInt8)) : RawStorage := s.toFinset

/-- `near-lean` as a `RuntimeInterface`. -/
noncomputable def nearLean (cfg : RuntimeConfig) : RuntimeInterface :=
  { Storage := List (List UInt8 × List UInt8)
    entries := rawOf
    Code := Wasm.Module × Nat
    Input := Input
    mkInput := mkInput
    Result := VMOutcome
    exec := fun (code, size) raw i => run cfg code size i.method (toVMContext i) raw
    failure := fun o => o.aborted.map (·.message)
    executionIssue := fun o => o.issue?.map (·.message)
    observationsValid := observationsValid
    outOfGas := fun o => (o.aborted.map (·.isOutOfGas)).getD false
    storage := (·.storage)
    balance := (·.balance)
    storageUsage := (·.storageUsage)
    burntGas := (·.burntGas)
    usedGas := (·.usedGas)
    returnValue := returnDataOf
    logs := (·.logs)
    promises := promisesOf
    encodeRet := encodeRet }

/-- The refinement obligation for the deployed binary under protocol parameters `cfg`. -/
@[blueprint "spec:refinement-near-lean"
  (statement := /-- \cref{spec:refinement} instantiated with the \texttt{near-lean} runtime (\texttt{NearVM.run}, the JSON argument and return encodings of near-sdk 3.1.0, receipts read back as the model's promises): the obligation on \texttt{contract.wasm} under protocol parameters $\mathit{cfg}$. -/)]
def RefinesNearLean (cfg : RuntimeConfig) (code : Wasm.Module) (size : Nat) (modelCfg : Config) : Prop :=
  Refines (nearLean cfg) (code, size) modelCfg

end WNear
