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

/-- A successful `U128` JSON string can contain only ASCII decimal digits and
an optional plus, literally or as Unicode escapes. All other decoded characters
would make Rust's integer parser fail. This specialized decoder is total. -/
def decodeU128String : List Char → Option (List Char)
  | ['"'] => some []
  | '\\' :: 'u' :: '0' :: '0' :: '3' :: digit :: rest => do
    if !digit.isDigit then none else
      pure (digit :: (← decodeU128String rest))
  | '\\' :: 'u' :: '0' :: '0' :: '2' :: hex :: rest => do
    if hex != 'b' && hex != 'B' then none else
      pure ('+' :: (← decodeU128String rest))
  | c :: rest => do
    if !c.isDigit && c != '+' then none else
      pure (c :: (← decodeU128String rest))
  | [] => none

def jsonWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- SDK 3.1.0 reads a JSON string then calls `u128::from_str_radix(_, 10)`.
Keep the projection total and reject non-JSON whitespace and integer overflow. -/
def parseU128Result (bytes : List UInt8) : Option Nat := do
  let text ← String.fromUTF8? ⟨bytes.toArray⟩
  let chars := ((text.toList.dropWhile jsonWhitespace).reverse.dropWhile jsonWhitespace).reverse
  let '"' :: body := chars | none
  let decoded ← decodeU128String body
  let digits := match decoded with | '+' :: rest => rest | other => other
  if digits.isEmpty || !digits.all Char.isDigit then none else do
    let amount := digits.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    if amount < u128Bound then some amount else none

/-- Every successfully projected callback amount satisfies the SDK integer bound. -/
theorem parseU128Result_lt {bytes : List UInt8} {amount : Nat}
    (h : parseU128Result bytes = some amount) : amount < u128Bound := by
  unfold parseU128Result at h
  simp only [bind, Option.bind] at h
  repeat (split at h <;> try simp_all)
  all_goals exact h.2.2 ▸ h.2.1

/-- Only result zero is read by wNEAR. Its raw representation is never replaced
by this projection when constructing the VM context. -/
def callbackResultOf (results : List Wasm.PromiseResult) : Option WNear.PromiseResult :=
  match results.head? with
  | none => none
  | some .notReady => some .notReady
  | some .failed => some .failed
  | some (.successful bytes) => some (.successful (parseU128Result bytes))

/-- A typed call and exact callback inputs, alongside chain-supplied resources. -/
structure Input where
  method : String
  args : String
  env : Env
  resources : ExecutionResources
  promiseResults : List Wasm.PromiseResult

def mkInput (resources : ExecutionResources) (results : List Wasm.PromiseResult)
    (env : Env) (call : Call) : Input :=
  { method := call.methodName, args := call.jsonArgs, env, resources, promiseResults := results }

def toVMContext (i : Input) : VMContext :=
  { currentAccountId := i.env.currentAccount.val.toUTF8.toList
    signerAccountId := i.env.predecessor.val.toUTF8.toList
    signerAccountPk := []
    predecessorAccountId := i.env.predecessor.val.toUTF8.toList
    input := i.args.toUTF8.toList
    promiseResults := i.promiseResults
    attachedDeposit := i.env.attachedDeposit
    prepaidGas := i.env.prepaidGas
    accountBalance := i.resources.balance
    storageUsage := i.resources.storageUsage }

/-- The adapter passes chain resources through without inventing funding. -/
theorem toVMContext_resources (resources : ExecutionResources) (results : List Wasm.PromiseResult)
    (env : Env) (call : Call) :
    (toVMContext (mkInput resources results env call)).accountBalance = resources.balance ∧
    (toVMContext (mkInput resources results env call)).storageUsage = resources.storageUsage :=
  ⟨rfl, rfl⟩

/-- Neither parse failures nor additional callback results are discarded. -/
theorem toVMContext_promiseResults (resources : ExecutionResources) (results : List Wasm.PromiseResult)
    (env : Env) (call : Call) :
    (toVMContext (mkInput resources results env call)).promiseResults = results := rfl

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
  | .promise _ => ""

def encodeRet : Ret → ReturnData
  | .unit => .value []
  | .promise index => .promise index
  | r => .value r.json.toUTF8.toList

def returnDataOf (o : VMOutcome) : ReturnData :=
  match o.returnData with
  | .value b => .value b
  | .receiptIndex index => .promise index
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

/-- Projection must preserve every receipt and the exact returned receipt
index. Returning a root or one of several chains is representable; refinement
compares the selected index against the model rather than guessing it. -/
def observationsValid (o : VMOutcome) : Bool :=
  (promisesOf? o).isSome &&
    match o.returnData with
    | .receiptIndex idx => idx < o.receipts.length
    | _ => true

/-- The storage as the model sees it. -/
def rawOf (s : List (List UInt8 × List UInt8)) : RawStorage := s.toFinset

/-- `near-lean` as a `RuntimeInterface`. -/
noncomputable def nearLean (cfg : RuntimeConfig) : RuntimeInterface :=
  { Storage := List (List UInt8 × List UInt8)
    entries := rawOf
    Code := Wasm.Module × Nat
    Input := Input
    CallbackResults := List Wasm.PromiseResult
    callbackResult := callbackResultOf
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
    subsidizedAmount := (·.subsidizedAmount)
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
