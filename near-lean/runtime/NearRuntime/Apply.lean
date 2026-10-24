import NearRuntime.Fees
import NearRuntime.State
import NearRuntime.Nonce
import NearRuntime.Refund
import NearRuntime.ActionValidation
import NearRuntime.TransactionSize
import NearRuntime.NativeIdentity
import NearRuntime.Base58
import NearInterface.Boundary

/-!
# `apply`

`runtime/src/lib.rs`: transactions become receipts, receipts execute their
actions, failures roll back and refund, data receipts resolve callbacks,
and everything that happens is reported as an `ExecutionOutcome`.
-/

namespace Near

open Wasm Wasm.Near

/-- IDs allocated by one successful VM action, in external creation order.
The action index is the original receipt action position, not a VM-call count. -/
structure VMIdentityBirth where
  actionIndex : Nat
  receipts : List ReceiptId
  data : List (DataId × AccountId)
  /-- The position of each data id in the action's data counter, which a yield also advances.
  Empty means the ids are numbered consecutively from zero. -/
  dataIndices : List Nat := []
  deriving Inhabited

/-- Final child order includes refunds and completion data. VM origins only
survive successful receipt execution; rollback discards their allocations. -/
structure ReceiptIdentityBirth where
  parent : ReceiptId
  children : List ReceiptId
  vmActions : List VMIdentityBirth
  /-- The native hash the children derive from, when it is not a registered receipt's: the
  data id of a yield whose timeout creates the child. -/
  parentHash : Option Bytes := none
  /-- Position of the first child among the receipts the hash derives, which a chunk's timeouts
  number together. -/
  startIndex : Nat := 0
  deriving Inhabited

structure ApplyResult where
  storageAccounting : Option TrieOverlay.State := none
  state : ChainState
  outgoing : List Receipt
  identityBirths : List ReceiptIdentityBirth := []
  /-- Persistent FIFO pops/appends, measured at the actual queue traversal. -/
  delayedConsumed : Nat := 0
  delayedAppended : Nat := 0
  /-- One outcome per transaction and per processed receipt, in order. -/
  outcomes : List (ReceiptId × ExecutionOutcome)
  /-- Outcome token burn plus failed system-refund deposits, minus what went
  to contracts as `burnt_gas_reward`. Includes price/penalty/creation settlement. -/
  tokensBurnt : Nat
  /-- Newly minted promise deposits, separate from positive gas burn. -/
  subsidizedAmount : Nat := 0
  /-- Validator proposals of the successful `Stake` actions, in the order the receipts ran. -/
  proposals : List ValidatorProposal := []
  /-- No state transition is committed when the model cannot execute a receipt.
  The state is the input state and the protocol observations are empty. -/
  issue : Option (ReceiptId × ExecutionIssue) := none

/-! ## Execution monad -/

/-- State threaded through one receipt: the chain state, the receipts and
outcomes produced so far, and the gas accounting of the receipt. -/
structure Exec where
  storageAccounting : Option TrieOverlay.State := none
  state : ChainState
  /-- Authority for administrative actions; creation changes it to the new
  receiver, as in nearcore's `actor_id`. -/
  actorId : AccountId := ""
  subsidizedAmount : Nat := 0
  newReceipts : List Receipt := []
  vmIdentityBirths : List VMIdentityBirth := []
  gasBurnt : Nat := 0
  /-- Gas burnt or attached onward; what is left of the receipt's gas is refunded. -/
  gasUsed : Nat := 0
  gasBurntForFunctionCall : Nat := 0
  /-- Receipt outcome burn, including price/penalty/creation settlement. -/
  tokensBurnt : Nat := 0
  /-- Tokens burnt by the actions themselves (global contract storage, the balance of a deleted
  gas key); a failed receipt burns none (`ActionReceiptResult::set_error`). -/
  actionTokensBurnt : Nat := 0
  /-- Failed system refunds burn their deposit outside the execution outcome. -/
  otherTokensBurnt : Nat := 0
  /-- Yocto credited to the contract out of its burnt gas (`burnt_gas_reward`). -/
  reward : Nat := 0
  logs : List String := []
  /-- Validator proposals of the receipt's `Stake` actions, in order; a failed receipt has none. -/
  proposals : List ValidatorProposal := []
  result : Option ExecutionStatus := none
  failureIndex : Option Nat := none
  deriving Inhabited

abbrev ExecM := ExceptT RuntimeError (StateM Exec)

def ExecM.fail (e : RuntimeError) : ExecM α := throw e

def getState : ExecM ChainState := do return (← get).state
def modifyState (f : ChainState → ChainState) : ExecM Unit := modify fun e => { e with state := f e.state }
def burnGas (n : Nat) : ExecM Unit := modify fun e => { e with gasBurnt := e.gasBurnt + n, gasUsed := e.gasUsed + n }
def useGas (n : Nat) : ExecM Unit := modify fun e => { e with gasUsed := e.gasUsed + n }
def emit (r : Receipt) : ExecM Unit := modify fun e => { e with newReceipts := e.newReceipts ++ [r] }
def fresh : ExecM Nat := do
  let e ← get
  let (id, st) := e.state.freshId
  set { e with state := st }
  return id

def liftExcept (e : Except RuntimeError α) : ExecM α :=
  match e with | .ok a => pure a | .error err => throw err

def getAccount (id : AccountId) : ExecM Account := do
  match (← getState).account? id with
  | some a => return a
  | none => throw (.accountDoesNotExist id)

def putAccount (id : AccountId) (a : Account) : ExecM Unit := modifyState (·.setAccount id a)

/-! ## Account id rules -/

/-- Can `predecessor` create `id`? The reserved system actor is neither top-level
nor a sub-account in near-account-id. Ordinary top-level names need the minimum
length (or registrar), and sub-accounts need their parent as predecessor. -/
def canCreateAccount (cfg : RuntimeConfig) (predecessor id : AccountId) : Bool :=
  if id == systemAccount then false
  else if accountIsImplicit cfg.wasm.ethImplicitAccounts id.toUTF8.toList then false
  else match id.splitOn "." with
    | [_] => id.length ≥ cfg.accountCreation.minAllowedTopLevelAccountLength
             || predecessor == cfg.accountCreation.registrarAccountId
    | parts => ".".intercalate (parts.drop 1) == predecessor

/-- The native reserved-actor rule cannot be bypassed by the registrar or by
changing the minimum top-level name length. -/
@[simp] theorem canCreateAccount_system (cfg : RuntimeConfig) (predecessor : AccountId) :
    canCreateAccount cfg predecessor systemAccount = false := by
  simp [canCreateAccount]

/-! ## Actions -/

def bytesOfString (s : String) : Bytes := s.toUTF8.toList
def stringOfBytes (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD ""

/-- Total structural conversion retains decoder issues in the code value.
The checked wrapper below rejects these issues before any receipts are committed. -/
def actionOfPromiseRaw (codeOf : Bytes → ContractCode) : PromiseAction → Action
  | .createAccount => .createAccount
  | .deployContract code => .deployContract (ContractCode.decodeSized codeOf code)
  | .functionCall m args amount gas => .functionCall (stringOfBytes m) args gas.toNat amount
  | .transfer amount => .transfer amount
  | .stake amount pk => .stake amount pk
  | .addKey pk nonce perm =>
    let permission : AccessKeyPermission := match perm with
      | .fullAccess => .fullAccess
      | .functionCall allowance receiver methods =>
        .functionCall allowance (stringOfBytes receiver)
          (decodeMethodNames methods)
      | .gasKeyFullAccess nonces => .gasKeyFullAccess 0 nonces
      | .gasKeyFunctionCall nonces allowance receiver methods =>
        .gasKeyFunctionCall 0 nonces allowance (stringOfBytes receiver)
          (decodeMethodNames methods)
    .addKey pk { nonce := nonce.toNat, permission }
  | .deleteKey pk => .deleteKey pk
  | .deleteAccount beneficiary => .deleteAccount (stringOfBytes beneficiary)
  | .useGlobalContract contract => .useGlobalContract contract
  | .deployGlobalContract code mode => .deployGlobalContract (ContractCode.decodeSized codeOf code) mode
  | .transferToGasKey pk amount => .transferToGasKey pk amount

/-- Missing external decoders are model issues, never silently deployable code. -/
def actionOfPromise (codeOf : Bytes → ContractCode) (action : PromiseAction) : Except RuntimeError Action := do
  let converted := actionOfPromiseRaw codeOf action
  if let .deployContract code := converted then
    if let some issue := code.decodeIssue then throw (.executionIssue issue)
  if let .deployGlobalContract code _ := converted then
    if let some issue := code.decodeIssue then throw (.executionIssue issue)
  return converted

/-- Context of a receipt being applied. -/
structure ReceiptCtx where
  cfg : RuntimeConfig
  ap : ApplyState
  receipt : Receipt
  action : ActionReceipt
  promiseResults : List PromiseResult
  /-- Per-action VM seed. The block's original seed stays in `ap`. -/
  vmRandomSeed : Option Bytes := none
  /-- Native hash of the executing action, the ancestor of the data ids its call generates. -/
  vmActionHash : Option Bytes := none
  /-- Data ids of the account's yields that a `promise_yield_resume` may still resume,
  as of the start of the receipt. nearcore divergence: yields created by an earlier action of the
  same receipt are not visible to a later one. -/
  vmYields : List Bytes := []
  /-- Decoder for code deployed by contracts (not available in Lean yet). -/
  codeOf : Bytes → ContractCode

/-- Exact VM context used by a receipt function-call action. -/
def functionCallContext (c : ReceiptCtx) (account : Account) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) (storageAccounting : Option TrieOverlay.State := none) : VMContext :=
  let id := c.receipt.receiverId
  {
    validateActionMethodUtf8 := true
    currentAccountId := bytesOfString id
    signerAccountId := bytesOfString c.action.signerId
    signerAccountPk := c.action.signerPublicKey
    predecessorAccountId := bytesOfString c.receipt.predecessorId
    input := args
    promiseResults := c.promiseResults
    blockHeight := c.ap.blockHeight
    blockTimestamp := c.ap.blockTimestamp
    epochHeight := c.ap.epochHeight
    accountBalance := account.amount
    accountLockedBalance := account.locked
    storageUsage := account.storageUsage
    attachedDeposit := deposit
    prepaidGas := gas
    randomSeed := c.vmRandomSeed.getD c.ap.randomSeed
    storageAccounting
    chargeStorageValueAccess := true
    outputDataReceivers := if isLast then c.action.outputDataReceivers.map fun d => bytesOfString d.receiverId else []
    actionHash := c.vmActionHash.getD []
    existingYields := c.vmYields
    chainId := bytesOfString c.ap.chainId
    validatorStake := c.ap.epochInfo.stake
    validatorTotalStake := c.ap.epochInfo.totalStake }

/-- Gas/log observations from one VM call, before its success/failure branch. -/
def Exec.recordVMOutcome (exec : Exec) (outcome : VMOutcome) : Exec :=
  { exec with
    storageAccounting := outcome.storageAccounting
    logs := exec.logs ++ outcome.logs
    gasBurntForFunctionCall := exec.gasBurntForFunctionCall + outcome.burntGas
    gasBurnt := exec.gasBurnt + outcome.burntGas
    gasUsed := exec.gasUsed + outcome.burntGas + (outcome.usedGas - outcome.burntGas) }

structure FunctionCallEffects where
  state : ChainState
  receipts : List Receipt
  result : ExecutionStatus

/-- Position in the action's data id counter of each data id the call's receipts depend on,
in creation order. A yield takes a slot of its own. -/
def dataIndicesOf (specs : List ReceiptSpec) : List Nat :=
  (specs.foldl (fun (acc : Nat × List Nat) spec =>
    match spec.yieldDataId with
    | some _ => (acc.1 + 1, acc.2)
    | none => (acc.1 + spec.dependencies.length,
        acc.2 ++ (List.range spec.dependencies.length).map (acc.1 + ·))) (0, [])).2

/-- Materialize the VM's ordered receipts and data dependencies without touching
execution gas. Id allocation and outgoing order match receipt execution: action receipts
(including yields) first, then the data receipts of resumed yields. -/
def materializeFunctionCallRaw (c : ReceiptCtx) (_isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) : FunctionCallEffects := Id.run do
  let id := c.receipt.receiverId
  let mut st := initial
  let mut receipts : List Receipt := []
  let mut ids : Array ReceiptId := #[]
  for _ in outcome.receipts do
    let (rid, next) := st.freshId
    st := next
    ids := ids.push rid
  let mut outputs : Array (List DataReceiver) := Array.replicate outcome.receipts.length []
  let mut inputs : Array (List DataId) := Array.replicate outcome.receipts.length []
  for h : i in [0:outcome.receipts.length] do
    let spec := outcome.receipts[i]
    for dep in spec.dependencies do
      let (dataId, next) := st.freshId
      st := next
      outputs := outputs.modify dep (· ++ [{ dataId, receiverId := stringOfBytes spec.receiverId }])
      inputs := inputs.modify i (· ++ [dataId])
  -- External result listeners are attached only after the entire action receipt
  -- succeeds. Local dependencies between newly created receipts are linked above.
  let outputReceivers : List DataReceiver := []
  let mut result := ExecutionStatus.successValue []
  match outcome.returnData with
  | .receiptIndex k =>
    outputs := outputs.modify k (· ++ outputReceivers)
    result := .successReceiptId (ids[k]?.getD 0)
  | .value v => result := .successValue v
  | .none => result := .successValue []
  for h : i in [0:outcome.receipts.length] do
    let spec := outcome.receipts[i]
    let actions := spec.actions.map (actionOfPromiseRaw c.codeOf)
    receipts := receipts ++ [{
      predecessorId := id
      receiverId := stringOfBytes spec.receiverId
      receiptId := ids[i]?.getD 0
      receipt := .action {
        signerId := c.action.signerId
        signerPublicKey := c.action.signerPublicKey
        gasPrice := c.action.gasPrice
        outputDataReceivers := outputs[i]?.getD []
        inputDataIds := inputs[i]?.getD []
        yieldDataId := spec.yieldDataId
        actions := actions } }]
  return { state := st, receipts, result }

/-- The data receipts of resumed yields go to the account itself, after the call's other receipts. -/
def resumeReceipts (account : AccountId) (resumes : List (Bytes × Bytes)) (initial : ChainState)
    (initialReceipts : List Receipt) : ChainState × List Receipt :=
  resumes.foldl (fun (acc : ChainState × List Receipt) resume =>
    let (rid, next) := acc.1.freshId
    (next, acc.2 ++ [{
      predecessorId := account
      receiverId := account
      receiptId := rid
      receipt := .data { dataId := 0, data := some resume.2, resumeDataId := some resume.1 } }]))
    (initial, initialReceipts)

/-- The timeout queue and the status of every yield a call created or resumed. -/
def yieldBookkeeping (c : ReceiptCtx) (outcome : VMOutcome) (initial : ChainState) : ChainState :=
  let id := c.receipt.receiverId
  let (first, next) := initial.yieldIndices.getD (0, 0)
  let created := outcome.receipts.filterMap (·.yieldDataId)
  let st := created.foldl (fun (st : ChainState) dataId =>
    { st with
      yieldTimeouts := st.yieldTimeouts ++ [(next + (created.idxOf dataId),
        { account := id, dataId, expiresAt := c.ap.blockHeight + c.cfg.wasm.limits.yieldTimeoutLengthInBlocks })]
      yieldStatus := Assoc.insert st.yieldStatus (id, dataId) .yielded }) initial
  let st := outcome.resumes.foldl (fun (st : ChainState) resume =>
    { st with yieldStatus := Assoc.insert st.yieldStatus (id, resume.1) .resumeInitiated }) st
  if created.isEmpty then st else { st with yieldIndices := some (first, next + created.length) }

/-- The data receipts of resumed yields (to the account itself) and the bookkeeping of the
yields a call created or resumed. Applied to the receipts the call produced, it comes after
them, as in `RuntimeExt`'s receipt manager. -/
def functionCallYields (c : ReceiptCtx) (outcome : VMOutcome) (effects : FunctionCallEffects) :
    FunctionCallEffects :=
  let resumed := resumeReceipts c.receipt.receiverId outcome.resumes effects.state effects.receipts
  { state := yieldBookkeeping c outcome resumed.1, receipts := resumed.2, result := effects.result }

/-- The entire promise set is checked before pure construction/commit. -/
def validateFunctionCallActions (c : ReceiptCtx) (outcome : VMOutcome) : Except RuntimeError Unit := do
  for spec in outcome.receipts do
    let _ ← spec.actions.mapM (actionOfPromise c.codeOf)
  pure ()

def materializeFunctionCall (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) : Except RuntimeError FunctionCallEffects := do
  validateFunctionCallActions c outcome
  return functionCallYields c outcome (materializeFunctionCallRaw c isLast outcome initial)

/-- A successful checked construction is exactly the pure stage, with no fallback actions. -/
theorem materializeFunctionCall_success (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (effects : FunctionCallEffects)
    (h : materializeFunctionCall c isLast outcome initial = .ok effects) :
    effects = functionCallYields c outcome (materializeFunctionCallRaw c isLast outcome initial) := by
  unfold materializeFunctionCall at h
  cases hv : validateFunctionCallActions c outcome with
  | error error => simp [hv, bind, Except.bind] at h
  | ok accepted => cases accepted; simpa [hv, bind, pure, Except.bind, Except.pure] using h.symm

/-- Commit successful VM effects; the gas/log record is updated separately. -/
def Exec.commitFunctionCall (exec : Exec) (outcome : VMOutcome) (effects : FunctionCallEffects) : Exec :=
  { exec with
    state := effects.state
    newReceipts := exec.newReceipts ++ effects.receipts
    vmIdentityBirths := exec.vmIdentityBirths ++ [{
      actionIndex := exec.failureIndex.getD 0
      receipts := effects.receipts.map (·.receiptId)
      data := effects.receipts.flatMap fun receipt => match receipt.receipt with
        | .data _ | .globalDistribution _ => []
        | .action action => action.inputDataIds.map (·, receipt.receiverId)
      dataIndices := dataIndicesOf outcome.receipts }]
    result := some effects.result
    subsidizedAmount := exec.subsidizedAmount + outcome.subsidizedAmount }

/-- Validate promised actions and materialize successful state changes before commit. -/
def functionCallEffects (c : ReceiptCtx) (account : Account) (outcome : VMOutcome)
    (isLast : Bool) (state : ChainState) : Except RuntimeError FunctionCallEffects :=
  let id := c.receipt.receiverId
  let state := state.setAccount id { account with amount := outcome.balance, storageUsage := outcome.storageUsage }
  let state := state.setContractStorage id outcome.storage
  materializeFunctionCall c isLast outcome state

/-- The contract an account runs: its own code, or the global code it points at. -/
def resolveContract (st : ChainState) (a : Account) : Option ContractCode :=
  match a.code with
  | some code => some code
  | none => a.global.bind st.globalCodeOf?

/-- Storage the account's contract identity accounts for (`get_contract_storage_usage`). -/
def Account.contractStorageUsage (a : Account) : Nat :=
  match a.code with
  | some code => code.size
  | none => (a.global.map Wasm.GlobalContractId.length).getD 0

/-- Execute a function call and turn its promises into receipts. -/
def applyFunctionCall (c : ReceiptCtx) (method : String) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) : ExecM Unit := do
  let account ← getAccount c.receipt.receiverId
  let st ← getState
  let some code := resolveContract st account
    | throw (.functionCallError (.compilationError "CodeDoesNotExist"))
  if let some issue := code.decodeIssue then throw (.executionIssue issue)
  let ctx := functionCallContext c account args gas deposit isLast (← get).storageAccounting
  let outcome := run c.cfg code.module code.size method ctx (st.contractStorage c.receipt.receiverId)
  modify (·.recordVMOutcome outcome)
  match outcome.aborted with
  | some err => throw (.functionCallError err)
  | none =>
    match functionCallEffects c account outcome isLast st with
    | .error error => throw error
    | .ok effects => modify (·.commitFunctionCall outcome effects)

/-- Account deletion stages all of its ContractData tombstones in the same
receipt overlay as VM writes; reads later in this chunk must see the deletion. -/
def stageContractStorageRemoval (account : AccountId) (storage : List (Bytes × Bytes))
    (accounting : Option TrieOverlay.State) : Option TrieOverlay.State :=
  accounting.map fun trie => storage.foldl (fun trie (key, _) =>
    trie.remove (TrieOverlay.contractKey account.toUTF8.toList key)) trie

/-- Sets the balance of a gas key permission. -/
def AccessKeyPermission.withGasBalance : AccessKeyPermission → Nat → AccessKeyPermission
  | .gasKeyFullAccess _ n, balance => .gasKeyFullAccess balance n
  | .gasKeyFunctionCall _ n allowance receiver methods, balance =>
    .gasKeyFunctionCall balance n allowance receiver methods
  | permission, _ => permission

/-- `GasKeyInfo::MAX_BALANCE_TO_BURN`: one NEAR. -/
def maxGasKeyBalanceToBurn : Nat := 1_000_000_000_000_000_000_000_000

/-- `Account::MAX_ACCOUNT_DELETION_STORAGE_USAGE`. -/
def maxAccountDeletionStorageUsage : Nat := 10_000

/-- Storage an added gas key costs (`gas_key_storage_cost`). -/
def gasKeyStorageCost (extra : Nat) (pk : PublicKey) (key : AccessKey) (nonces : Nat) : Nat :=
  accessKeyStorageBytes pk key + extra + gasKeyNonceStorageBytes extra pk nonces

/-- `check_actor_permissions` for the gas key withdrawal: the key must be a gas key. -/
def gasKeyOf (st : ChainState) (id : AccountId) (pk : PublicKey) : Except RuntimeError (AccessKey × Nat × Nat) :=
  if (st.account? id).isNone then .error (.accountDoesNotExist id) else
  match st.accessKey? id pk with
  | some key =>
    match key.permission.gasKeyInfo? with
    | some (balance, nonces) => .ok (key, balance, nonces)
    | none => .error (.gasKeyDoesNotExist id pk)
  | none => .error (.gasKeyDoesNotExist id pk)

/-- `action_transfer_to_gas_key`: credit the key's balance. -/
def gasKeyDeposit (st : ChainState) (id : AccountId) (pk : PublicKey) (deposit : Nat) :
    Except RuntimeError ChainState := do
  let (key, balance, _) ← gasKeyOf st id pk
  return st.setAccessKey id pk { key with permission := key.permission.withGasBalance (balance + deposit) }

/-- `action_withdraw_from_gas_key`: move the amount from the key's balance to the account's. -/
def gasKeyWithdrawal (st : ChainState) (id : AccountId) (pk : PublicKey) (amount : Nat) :
    Except RuntimeError ChainState := do
  let (key, balance, _) ← gasKeyOf st id pk
  if balance < amount then throw (.insufficientGasKeyBalance id pk balance amount)
  let st := st.setAccessKey id pk { key with permission := key.permission.withGasBalance (balance - amount) }
  match st.account? id with
  | some a => return st.setAccount id { a with amount := a.amount + amount }
  | none => throw (.accountDoesNotExist id)

def Exec.burnAction (exec : Exec) (amount : Nat) : Exec :=
  { exec with actionTokensBurnt := exec.actionTokensBurnt + amount }

/-- `validate_delegate_action_key`: the delegate's key, nonce and permission. It returns the
nonce lane of a gas key (`none` for an ordinary key). -/
def delegateKeyCheck (c : ReceiptCtx) (st : ChainState) (sender : AccountId) (pk : PublicKey)
    (nonce : Nat) (nonceIndex : Option Nat) (inner : List Action) (receiver : AccountId) :
    Except RuntimeError (Option Nat) := do
  if (st.account? sender).isNone then throw (.accountDoesNotExist sender)
  let some key := st.accessKey? sender pk
    | throw (.delegateActionAccessKeyError s!"AccessKeyNotFound {sender} {repr pk}")
  let (current, lane) ← match nonceIndex with
    | none =>
      if key.permission.gasKeyInfo?.isSome then
        throw (.delegateActionAccessKeyError "DelegateActionRequiresNonGasKey")
      pure (key.nonce, none)
    | some index =>
      let some (_, nonces) := key.permission.gasKeyInfo?
        | throw (.delegateActionAccessKeyError "DelegateActionRequiresGasKey")
      if index ≥ nonces then throw (.delegateActionInvalidNonceIndex index nonces)
      pure ((st.gasKeyNonce? sender pk index).getD 0, some index)
  if nonce ≤ current then throw (.delegateActionInvalidNonce nonce current)
  let upperBound := c.ap.blockHeight * 1_000_000
  if nonce ≥ upperBound then throw (.delegateActionNonceTooLarge nonce upperBound)
  if let some (allowanceKeyReceiver, methods) :=
      (match key.permission with
        | .functionCall _ r m | .gasKeyFunctionCall _ _ _ r m => some (r, m)
        | _ => none) then
    match inner with
    | [.functionCall method _ _ deposit] =>
      if deposit > 0 then
        throw (.delegateActionAccessKeyError "DepositWithFunctionCall")
      if receiver != allowanceKeyReceiver then
        throw (.delegateActionAccessKeyError s!"ReceiverMismatch {receiver} {allowanceKeyReceiver}")
      unless methods.isEmpty || methods.contains method do
        throw (.delegateActionAccessKeyError s!"MethodNameMismatch {method}")
    | _ => throw (.delegateActionAccessKeyError "RequiresFullAccess")
  return lane

/-- The delegate's nonce moves: the key's own nonce, or the lane of a gas key. -/
def delegateKeyUpdate (st : ChainState) (sender : AccountId) (pk : PublicKey) (lane : Option Nat)
    (nonce : Nat) : ChainState :=
  match lane with
  | none =>
    match st.accessKey? sender pk with
    | some key => st.setAccessKey sender pk { key with nonce }
    | none => st
  | some index => st.setGasKeyNonce sender pk index nonce

/-- `validate_delegate_action_key` with the nonce update applied on success. -/
def delegateKeyState (c : ReceiptCtx) (st : ChainState) (sender : AccountId) (pk : PublicKey)
    (nonce : Nat) (nonceIndex : Option Nat) (inner : List Action) (receiver : AccountId) :
    Except RuntimeError ChainState := do
  let lane ← delegateKeyCheck c st sender pk nonce nonceIndex inner receiver
  return delegateKeyUpdate st sender pk lane nonce

/-- The checks of `apply_delegate_action` that precede the key: signature, expiry, sender. -/
def delegateChecks (c : ReceiptCtx) (act : Action) : Except RuntimeError Unit :=
  match act with
  | .delegate sender _ inner _ _ maxHeight _ _ _ =>
    -- nearcore types the inner actions as `NonDelegateAction`, so a nested delegate cannot occur.
    if inner.any Action.isDelegate then
      .error (.executionIssue (.unsupportedAction "nested delegate action"))
    else if !c.ap.verifyDelegate act then .error .delegateActionInvalidSignature
    else if c.ap.blockHeight > maxHeight then .error .delegateActionExpired
    else if sender != c.receipt.receiverId then
      .error (.delegateActionSenderDoesNotMatchTxReceiver sender c.receipt.receiverId)
    else .ok ()
  | _ => .ok ()

/-- The state after a delegate action's key checks (the nonce moves), for the delegate action. -/
def delegateState (c : ReceiptCtx) (st : ChainState) (act : Action) : Except RuntimeError ChainState :=
  match act with
  | .delegate sender receiver inner nonce nonceIndex _ pk _ _ =>
    delegateKeyState c st sender pk nonce nonceIndex inner receiver
  | _ => .ok st

/-- Gas the relayer prepaid for the receipt a delegate action creates, which that receipt
will consume. -/
def delegateRequired (c : ReceiptCtx) (act : Action) : Nat :=
  match act with
  | .delegate _ receiver inner .. =>
    c.cfg.fees.actionFees.newActionReceipt.execution
      + Fees.prepaidExecList c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts receiver inner
      + Fees.totalPrepaid inner
  | _ => 0

/-- The receipt carrying a delegate action's inner actions on behalf of the sender. -/
def delegateReceipt (c : ReceiptCtx) (act : Action) (id : ReceiptId) : Receipt :=
  match act with
  | .delegate sender receiver inner .. =>
    { predecessorId := sender, receiverId := receiver, receiptId := id
      receipt := .action {
        signerId := c.action.signerId
        signerPublicKey := c.action.signerPublicKey
        gasPrice := c.action.gasPrice
        actions := inner } }
  | _ => { predecessorId := "", receiverId := "", receiptId := id, receipt := .data { dataId := 0, data := none } }

/-- `apply_delegate_action`: check the signed action, advance the sender's nonce and emit the
receipt carrying the inner actions, whose execution and sending the relayer already paid for.
nearcore divergence: the send fees of the inner actions are computed for each delegate action,
where nearcore sums them over all actions of the receipt before it burns them; the totals agree
whenever a receipt carries one delegate action. Access-key failures of the delegate (key
missing, nonce, permission) carry their description as text instead of nearcore's structured
`InvalidAccessKeyError`. -/
def applyDelegateAction (c : ReceiptCtx) (act : Action) : ExecM Unit := do
  liftExcept (delegateChecks c act)
  let st ← getState
  let moved ← liftExcept (delegateState c st act)
  modifyState fun _ => moved
  useGas (delegateRequired c act)
  burnGas (Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts act)
  let id ← fresh
  emit (delegateReceipt c act id)

/-- What `action_deploy_global_contract` decides before anything changes: the paying account,
the identifier, the distribution nonce and the storage cost to burn. -/
structure DeployGlobalPlan where
  account : Account
  identifier : Wasm.GlobalContractId
  nonce : Nat
  burn : Nat

def planDeployGlobal (c : ReceiptCtx) (st : ChainState) (account : Account) (code : ContractCode)
    (mode : GlobalDeployMode) : Except RuntimeError DeployGlobalPlan := do
  let id := c.receipt.receiverId
  if let some issue := code.decodeIssue then throw (.executionIssue issue)
  -- nearcore divergence: before `IncludeDeployGlobalContractOutcomeBurntStorage` the storage cost is
  -- burnt without appearing in the outcome's burnt tokens; only the protocols that report it are modelled.
  unless c.cfg.includeDeployGlobalContractOutcomeBurntStorage do
    throw (.executionIssue (.unsupportedAction "deploy global contract without burnt storage in the outcome"))
  let cost := c.cfg.globalContractStorageAmountPerByte * code.size
  if account.amount < cost then throw (.lackBalanceForState id cost)
  let identifier : Wasm.GlobalContractId ← match mode with
    | .accountId => pure (.accountId (bytesOfString id))
    | .codeHash =>
      match Base58.decode code.hash with
      | some hash => pure (.codeHash hash)
      | none => throw (.executionIssue (.unsupportedAction "global contract code hash"))
  return { account := { account with amount := account.amount - cost }, identifier
           nonce := if c.cfg.globalContractDistributionNonce then st.globalNonce identifier + 1 else 0
           burn := cost }

/-- `action_deploy_global_contract`: the storage is paid for by burning, and a distribution
receipt carries the code to every shard. -/
def applyDeployGlobalContract (c : ReceiptCtx) (code : ContractCode) (mode : GlobalDeployMode) :
    ExecM Unit := do
  let id := c.receipt.receiverId
  let a ← getAccount id
  let st ← getState
  let plan ← liftExcept (planDeployGlobal c st a code mode)
  modify (·.burnAction plan.burn)
  putAccount id plan.account
  modifyState (·.setGlobalNonceIf c.cfg.globalContractDistributionNonce plan.identifier plan.nonce)
  let rid ← fresh
  emit {
    predecessorId := id
    receiverId := systemReceiver
    receiptId := rid
    receipt := .globalDistribution { id := plan.identifier, targetShard := c.ap.shardId, code, nonce := plan.nonce } }

/-- The account a transfer creates for an ETH-implicit or deterministic receiver
(`action_implicit_account_creation_transfer`): ETH-implicit accounts use the wallet global contract.
nearcore divergence: before `EthImplicitGlobalContract` the wallet contract is deployed as local code
(`near[wallet contract hash]` magic bytes); that protocol range is reported as unsupported. -/
def specialImplicitAccount (c : ReceiptCtx) (id : AccountId) (deposit : Nat) :
    Except RuntimeError (Option Account) :=
  if !c.cfg.wasm.ethImplicitAccounts then .ok none
  else match accountKind (bytesOfString id) with
    | .ethImplicit =>
      if c.cfg.wasm.ethImplicitGlobalContract then
        .ok (some { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount + 32
                    global := some (.codeHash (ethWalletGlobalContractHash c.ap.chainId)), versionTwo := true })
      else .error (.executionIssue (.unsupportedAction "ETH-implicit account creation with the legacy wallet contract"))
    | .nearDeterministic => .ok (some { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount })
    | _ => .ok none

def applyAction (c : ReceiptCtx) (isLast : Bool) : Action → ExecM Unit
  | .createAccount => do
    let id := c.receipt.receiverId
    if (← getState).account? id |>.isSome then throw (.accountAlreadyExists id)
    unless canCreateAccount c.cfg c.receipt.predecessorId id do
      if id != systemAccount && (id.splitOn ".").length == 1 then
        throw (.createAccountOnlyByRegistrar id c.cfg.accountCreation.registrarAccountId c.receipt.predecessorId)
      throw (.createAccountNotAllowed id c.receipt.predecessorId)
    putAccount id { amount := 0, storageUsage := c.cfg.fees.numBytesAccount }
    modify fun e => { e with actorId := id }
  | .deployContract code => do
    if let some issue := code.decodeIssue then throw (.executionIssue issue)
    let id := c.receipt.receiverId
    let a ← getAccount id
    if code.size > c.cfg.wasm.limits.maxContractSize then
      throw (.contractSizeExceeded code.size c.cfg.wasm.limits.maxContractSize)
    putAccount id { a with
      code := some code
      global := none
      storageUsage := (a.storageUsage - a.contractStorageUsage) + code.size }
  | .functionCall m args gas deposit => applyFunctionCall c m args gas deposit isLast
  | .transfer deposit => do
    let id := c.receipt.receiverId
    match (← getState).account? id with
    | some a => do
      putAccount id { a with amount := a.amount + deposit }
      if c.receipt.isGasRefund then
        modifyState (·.refundAllowance id c.action.signerPublicKey deposit)
    | none =>
      -- implicit account creation on transfer
      match ← liftExcept (specialImplicitAccount c id deposit) with
      | some account =>
        putAccount id account
        modify fun e => { e with actorId := id }
      | none =>
        if let some pk := implicitPublicKey? id then
          let key : AccessKey := { nonce := initialNonce c.ap.blockHeight, permission := .fullAccess }
          putAccount id { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount
            + accessKeyStorageBytes pk key
            + c.cfg.fees.numExtraBytesRecord }
          modifyState (·.setAccessKey id pk key)
          modify fun e => { e with actorId := id }
        else throw (.accountDoesNotExist id)
  | .stake stake pk => do
    -- `action_stake`: the locked balance grows out of the liquid one, a proposal goes to the epoch.
    let id := c.receipt.receiverId
    let a ← getAccount id
    let increment := stake - a.locked
    if a.amount < increment then throw (.triesToStake id stake a.locked a.amount)
    if a.locked == 0 && stake == 0 then throw (.triesToUnstake id)
    let minimum := c.ap.epochInfo.minimumStake
    if stake > 0 && stake < minimum then throw (.insufficientStake id stake minimum)
    modify fun e => { e with proposals := e.proposals ++ [{ account := id, publicKey := pk, stake }] }
    if stake > a.locked then
      putAccount id { a with amount := a.amount - increment, locked := stake }
  | .addKey pk key => do
    let id := c.receipt.receiverId
    let st ← getState
    if (st.accessKey? id pk).isSome then throw (.addKeyAlreadyExists id pk)
    let a ← getAccount id
    let extra := c.cfg.fees.numExtraBytesRecord
    match key.permission.gasKeyInfo? with
    | some (_, nonces) =>
      -- A new gas key starts empty: action validation rejects a gas key added with a balance.
      let stored : AccessKey := { key with nonce := 0, permission := key.permission.withGasBalance 0 }
      putAccount id { a with storageUsage := a.storageUsage + gasKeyStorageCost extra pk stored nonces }
      modifyState fun st => (List.range nonces).foldl
        (fun st lane => st.setGasKeyNonce id pk lane (initialNonce c.ap.blockHeight))
        (st.setAccessKey id pk stored)
    | none =>
      putAccount id { a with storageUsage := a.storageUsage + accessKeyStorageBytes pk key + extra }
      modifyState (·.setAccessKey id pk { key with nonce := initialNonce c.ap.blockHeight })
  | .deleteKey pk => do
    let id := c.receipt.receiverId
    let st ← getState
    let some key := st.accessKey? id pk | throw (.deleteKeyDoesNotExist id pk)
    let a ← getAccount id
    let extra := c.cfg.fees.numExtraBytesRecord
    match key.permission.gasKeyInfo? with
    | some (balance, nonces) =>
      if balance > maxGasKeyBalanceToBurn then throw (.gasKeyBalanceTooHigh id (some pk) balance)
      modify (·.burnAction balance)
      putAccount id { a with storageUsage := a.storageUsage - gasKeyStorageCost extra pk key nonces }
      modifyState fun st => (st.removeAccessKey id pk).removeGasKeyNonces id pk
    | none =>
      putAccount id { a with storageUsage := a.storageUsage - (accessKeyStorageBytes pk key + extra) }
      modifyState (·.removeAccessKey id pk)
  | .deleteAccount beneficiary => do
    let id := c.receipt.receiverId
    unless isLast do throw .deleteActionMustBeFinal
    let a ← getAccount id
    if a.locked > 0 then throw (.deleteAccountStaking id)
    let st ← getState
    let contract := if c.cfg.fixDeleteAccountGlobalContractStorageUsage then a.contractStorageUsage
      else (a.code.map (·.size)).getD 0
    if a.storageUsage - contract > maxAccountDeletionStorageUsage then
      throw (.deleteAccountWithLargeState id)
    let gasKeys := st.gasKeyBalances id
    if gasKeys > maxGasKeyBalanceToBurn then throw (.gasKeyBalanceTooHigh id none gasKeys)
    let (r, st') := refundReceipt st beneficiary a.amount
    modify fun exec => { exec with
      state := st'.removeAccount id
      storageAccounting := stageContractStorageRemoval id (st'.contractStorage id) exec.storageAccounting }
    modify (·.burnAction gasKeys)
    modify fun e => { e with actorId := c.receipt.predecessorId }
    if a.amount > 0 then emit r
  | .useGlobalContract contract => do
    let id := c.receipt.receiverId
    unless ((← getState).globalCodeOf? contract).isSome do throw (.globalContractDoesNotExist contract)
    let a ← getAccount id
    putAccount id { a with
      code := none
      global := some contract
      versionTwo := true
      storageUsage := (a.storageUsage - a.contractStorageUsage) + contract.length }
  | .deployGlobalContract code mode => applyDeployGlobalContract c code mode
  | .transferToGasKey pk deposit => do
    let moved ← liftExcept (gasKeyDeposit (← getState) c.receipt.receiverId pk deposit)
    modifyState fun _ => moved
  | .withdrawFromGasKey pk amount => do
    let moved ← liftExcept (gasKeyWithdrawal (← getState) c.receipt.receiverId pk amount)
    modifyState fun _ => moved
  | act@(.delegate ..) => applyDelegateAction c act

/-- `check_storage_stake` on one account. The formula, with the NEP-448
zero-balance exemption, is the boundary's `NearInterface.stakeDeficit`. -/
def storageStakeDeficit (cfg : RuntimeConfig) (a : Account) : Nat :=
  NearInterface.stakeDeficit cfg a.storageUsage a.amount a.locked

def checkStorageStake (cfg : RuntimeConfig) (id : AccountId) : ExecM Unit := do
  match (← getState).account? id with
  | some a =>
    let deficit := storageStakeDeficit cfg a
    if deficit > 0 then throw (.lackBalanceForState id deficit)
  | none => pure ()

/-! ## Receipts -/

/-- Account existence is checked before permission for each individual action.
Implicit account creation requires a sole transfer from a non-system sender.
Reference: `actions.rs::check_account_existence` at `runtime/reference.json`. -/
def checkActionAccount (st : ChainState) (r : Receipt) (onlyAction : Bool)
    (action : Action) (ethEnabled : Bool) : Except RuntimeError Unit :=
  let accountExists := (st.account? r.receiverId).isSome
  match action with
  | .createAccount =>
    if accountExists then .error (.accountAlreadyExists r.receiverId)
    else if accountIsImplicit ethEnabled (bytesOfString r.receiverId) then .error (.onlyImplicitAccountCreationAllowed r.receiverId)
    else .ok ()
  | .transfer _ =>
    if accountExists || (onlyAction && !r.isRefund && accountIsImplicit ethEnabled (bytesOfString r.receiverId)) then .ok ()
    else .error (.accountDoesNotExist r.receiverId)
  | _ => if accountExists then .ok () else .error (.accountDoesNotExist r.receiverId)

/-- Administrative actions require receiver authority. A function call or
transfer never grants the predecessor authority over an existing account. -/
def checkActorPermissions (actor receiver : AccountId) (action : Action) : Except RuntimeError Unit :=
  match action with
  | .deployContract _ | .stake .. | .addKey .. | .deleteKey _ | .deleteAccount _ | .useGlobalContract _
  | .deployGlobalContract .. | .withdrawFromGasKey .. =>
    if actor == receiver then .ok () else .error (.actorNoPermission receiver actor)
  | _ => .ok ()

def Action.requiresActor : Action → Bool
  | .deployContract _ | .stake .. | .addKey .. | .deleteKey _ | .deleteAccount _ | .useGlobalContract _
  | .deployGlobalContract .. | .withdrawFromGasKey .. => true
  | _ => false

theorem administrative_action_authorized (actor receiver : AccountId) (action : Action)
    (admin : action.requiresActor = true)
    (allowed : checkActorPermissions actor receiver action = .ok ()) : actor = receiver := by
  cases action <;> simp_all [Action.requiresActor, checkActorPermissions]

/-- A foreign actor cannot deploy code to an existing receiver. -/
theorem foreign_deploy_denied (actor receiver : AccountId) (code : ContractCode)
    (h : actor ≠ receiver) :
    checkActorPermissions actor receiver (.deployContract code) =
      .error (.actorNoPermission receiver actor) := by
  simp [checkActorPermissions, h]

/-- Admission checks are ordered per action and do not charge gas. -/
def checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (act : Action) : ExecM Unit := do
  match checkActionAccount (← getState) c.receipt onlyAction act c.cfg.wasm.ethImplicitAccounts with
  | .error e => throw e
  | .ok () => pure ()
  match checkActorPermissions (← get).actorId c.receipt.receiverId act with
  | .error e => throw e
  | .ok () => pure ()

/-- Receipt gas observations include system execution; settlement exempts its token charge. -/
def chargeReceiptFee (isRefund : Bool) (fee : Nat) : ExecM Unit :=
  let _ := isRefund
  burnGas fee

/-- One action's protocol fees, admission checks and body, in execution order. -/
def runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (act : Action) : ExecM Unit := do
  chargeReceiptFee c.receipt.isRefund (Fees.exec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId act)
  checkReceiptAction c onlyAction act
  applyAction c isLast act

-- nearcore divergence: with `nativeReceiptHashes = none` a call sees the block (or supplied)
-- seed directly rather than `create_random_seed(action_hash, random_seed)`.
/-- Native VM randomness uses this receipt's original action position and
current execution height, including delayed and postponed receipt execution.
Missing/malformed exact-mode inputs are errors, never direct-seed fallbacks. -/
def actionRandomSeed (c : ReceiptCtx) (index : Nat) : Except String Bytes := do
  match c.ap.nativeReceiptHashes with
  | none => pure (c.vmRandomSeed.getD c.ap.randomSeed)
  | some bindings =>
    NativeIdentity.validate bindings
    let parent ← NativeIdentity.resolve bindings c.receipt.receiptId
    let action ← NativeIdentity.action parent c.ap.blockHeight index
    NativeIdentity.randomSeed action c.ap.randomSeed

/-- The native hash of the action at `index`, from which the data ids of its call derive. Without
native receipt hashes there is none and the call numbers its ids from an empty hash. -/
def actionHashOf (c : ReceiptCtx) (index : Nat) : Option Bytes :=
  match c.ap.nativeReceiptHashes with
  | none => none
  | some bindings =>
    match NativeIdentity.resolve bindings c.receipt.receiptId with
    | .ok parent => (NativeIdentity.action parent c.ap.blockHeight index).toOption
    | .error _ => none

/-- Derivation is local to one call: later actions still start from the block
seed, while non-VM actions need no random context. Invalid exact-mode context
is a model issue and rolls back the chunk rather than failing a contract. -/
def runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool) (act : Action) (index : Nat) : ExecM Unit :=
  match act with
  | .functionCall .. =>
    match actionRandomSeed c index with
    | .error error => throw (.executionIssue (.interpreterError s!"Native action randomness context: {error}"))
    | .ok seed =>
      runReceiptAction { c with vmRandomSeed := some seed, vmActionHash := actionHashOf c index } onlyAction isLast act
  | _ => runReceiptAction c onlyAction isLast act

/-- Explicit ordered traversal, stopping at the first action error. -/
def runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) : List Action → Nat → ExecM Unit
  | [], _ => pure ()
  | act :: rest, index => do
    modify fun e => { e with failureIndex := some index }
    runReceiptActionAt c onlyAction rest.isEmpty act index
    runReceiptActionList c onlyAction rest (index + 1)

/-- Complete action attempt, before receipt rollback and finalization. -/
def receiptActionBody (c : ReceiptCtx) : ExecM Unit := do
  chargeReceiptFee c.receipt.isRefund c.cfg.fees.actionFees.newActionReceipt.execution
  runReceiptActionList c (c.action.actions.length == 1) c.action.actions 0
  modify fun e => { e with failureIndex := none }
  checkStorageStake c.cfg c.receipt.receiverId

/-- Run actions and the final storage-staking check, before rollback/refunds. -/
def runReceiptActions (c : ReceiptCtx) (st0 : ChainState) : Exec × Option RuntimeError :=
  let exec0 : Exec := { state := st0, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting }
  match ((receiptActionBody c).run.run exec0) with
    | (.ok (), e) => (e, none)
    | (.error err, e) => (e, some err)

/-- Receipt failure restores the pre-action state while retaining gas and logs. -/
def rollbackReceipt (st0 : ChainState) (exec : Exec) (failed : Option RuntimeError) : Exec :=
  match failed with
    | some err => { exec with state := st0, storageAccounting := exec.storageAccounting.map (fun trie => { trie with prospective := [] }), newReceipts := [], proposals := [], vmIdentityBirths := [], subsidizedAmount := 0, actionTokensBurnt := 0, gasUsed := exec.gasBurnt,
                              result := some (.failure err) }
    | none => exec

def Exec.addBalanceRefund (exec : Exec) (receiver : AccountId) (amount : Nat) : Exec :=
  let (r, st) := refundReceipt exec.state receiver amount
  { exec with state := st, newReceipts := exec.newReceipts ++ [r] }

def Exec.addGasRefund (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat) : Exec :=
  let (r, st) := gasRefundReceipt exec.state receiver pk amount
  { exec with state := st, newReceipts := exec.newReceipts ++ [r] }

def Exec.receiptRewardAmount (exec : Exec) (cfg : RuntimeConfig) (burnPrice purchasePrice : Nat) : Nat :=
  let (num, den) := cfg.fees.burntGasReward
  let price := if cfg.accountCostIncrease then burnPrice else purchasePrice
  exec.gasBurntForFunctionCall * num / den * price

/-- Reward comes from burnt tokens and is computed after rollback. -/
def Exec.creditReceiptReward (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) : Exec :=
  let reward := exec.receiptRewardAmount cfg burnPrice purchasePrice
  match exec.state.account? receiver with
  | some a => { exec with
      state := exec.state.setAccount receiver { a with amount := a.amount + reward }
      reward := reward }
  | none => { exec with reward := 0 }

/-- One failure data output allocates an id and carries no funds. -/
def failureDataStep (receiver : AccountId) (acc : ChainState × List Receipt) (d : DataReceiver) :
    ChainState × List Receipt :=
  let (st, rs) := acc
  let (id, st) := st.freshId
  (st, rs ++ [{
    predecessorId := receiver
    receiverId := d.receiverId
    receiptId := id
    receipt := .data { dataId := d.dataId, data := none } }])

/-- Failed outputs propagate `none`, with no token backing. -/
def Exec.addFailureData (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) : Exec :=
  let (st, rs) := outputs.foldl (failureDataStep receiver) (exec.state, [])
  { exec with state := st, newReceipts := exec.newReceipts ++ rs }

/-- Successful result data has the same envelope/dependency identities as
failure data; only its payload differs. -/
def successDataStep (receiver : AccountId) (bytes : Bytes) (acc : ChainState × List Receipt)
    (d : DataReceiver) : ChainState × List Receipt :=
  let (st, rs) := acc
  let (id, st) := st.freshId
  (st, rs ++ [{
    predecessorId := receiver
    receiverId := d.receiverId
    receiptId := id
    receipt := .data { dataId := d.dataId, data := some bytes } }])

def Exec.addSuccessData (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (bytes : Bytes) : Exec :=
  let (st, rs) := outputs.foldl (successDataStep receiver bytes) (exec.state, [])
  { exec with state := st, newReceipts := exec.newReceipts ++ rs }

/-- Return forwarding changes routing metadata, not the selected receipt's
identity, action body or funds. VM validation supplies an existing action target. -/
def Receipt.forwardResult (receipt : Receipt) (target : ReceiptId) (outputs : List DataReceiver) : Receipt :=
  if receipt.receiptId == target then
    match receipt.receipt with
    | .action action =>
      { receipt with receipt := .action { action with outputDataReceivers := action.outputDataReceivers ++ outputs } }
    | .data _ | .globalDistribution _ => receipt
  else receipt

def Exec.forwardResult (exec : Exec) (target : ReceiptId) (outputs : List DataReceiver) : Exec :=
  { exec with newReceipts := exec.newReceipts.map (fun receipt => receipt.forwardResult target outputs) }

/-- Complete the whole action receipt: values (including empty transfer results)
emit data, failures emit failed data, and a returned receipt inherits listeners.
This runs after storage checks, rollback, refunds and reward settlement. -/
def Exec.deliverResult (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) : Exec :=
  match exec.result.getD (.successValue []) with
  | .successValue bytes => exec.addSuccessData receiver outputs bytes
  | .failure _ => exec.addFailureData receiver outputs
  | .successReceiptId target => exec.forwardResult target outputs

/-- Select the final action's result before delivering the complete receipt.
Non-call actions return the empty value even if an earlier call returned a promise. -/
def Exec.finishReceiptResult (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) : Exec :=
  let exec := if failed.isNone && c.action.actions.getLast?.any (fun action => !action.isFunctionCall) then
      { exec with result := none } else exec
  exec.deliverResult c.receipt.receiverId c.action.outputDataReceivers

/-- Finalize a receipt attempt: rollback, settlement, refunds, reward and data. -/
def finalizeReceipt (c : ReceiptCtx) (st0 : ChainState) (exec : Exec) (failed : Option RuntimeError) : Exec :=
  let receiver := c.receipt.receiverId
  let receiptGas := Fees.receiptGasBudget c.cfg receiver c.action.actions
  let isRefund := c.receipt.isRefund
  let exec := rollbackReceipt st0 exec failed
  -- refunds: unspent gas to the signer, the deposits to the predecessor on failure
  let createdAccount := (st0.account? receiver).isNone && (exec.state.account? receiver).isSome
    && failed.isNone
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice receiptGas
    exec.gasUsed exec.gasBurnt createdAccount
  let tokensRefund := if isRefund then 0 else settlement.refund
  let exec := { exec with
    tokensBurnt := (if isRefund then 0 else settlement.tokensBurnt) + exec.actionTokensBurnt
    otherTokensBurnt := if isRefund && failed.isSome then Fees.totalDeposit c.action.actions else 0
  }
  let depositRefund := if failed.isSome then Fees.totalDeposit c.action.actions else 0
  let exec := if depositRefund > 0 && c.receipt.predecessorId != systemAccount then
      exec.addBalanceRefund c.receipt.predecessorId depositRefund
    else exec
  let exec := if tokensRefund > 0 && c.action.signerId != systemAccount then
      exec.addGasRefund c.action.signerId c.action.signerPublicKey tokensRefund
    else exec
  let exec := exec.creditReceiptReward c.cfg receiver settlement.burnPrice c.action.gasPrice
  let exec := exec.finishReceiptResult c failed
  { exec with result := some (exec.result.getD (.successValue [])) }


/-- Publish successful receipt writes without rebuilding the chunk base trie.
Failures have already cleared prospective writes; cached hashes are unchanged. -/
def Exec.commitStorage (exec : Exec) : Exec :=
  { exec with storageAccounting := exec.storageAccounting.map (fun trie =>
    { trie with committed := trie.prospective.foldl (fun changes (key, value) =>
        (key, value) :: changes.filter (·.1 != key)) trie.committed, prospective := [] }) }

/-- Execute and finalize the actual action receipt. -/
def applyActionReceipt (c : ReceiptCtx) (st0 : ChainState) : Exec :=
  let (exec, failed) := runReceiptActions c st0
  (finalizeReceipt c st0 exec failed).commitStorage

/-- Outcome of an executed receipt. -/
def outcomeOf (r : Receipt) (e : Exec) : ExecutionOutcome :=
  { failureIndex := e.failureIndex
    executorId := r.receiverId
    status := e.result.getD (.successValue [])
    logs := e.logs
    -- Native execution outcomes list action receipts, excluding data envelopes.
    receiptIds := e.newReceipts.filterMap (fun receipt =>
      match receipt.receipt with
      | .action _ => some receipt.receiptId
      | .data _ | .globalDistribution _ => none)
    gasBurnt := e.gasBurnt
    tokensBurnt := e.tokensBurnt
    proposals := e.proposals }

/-- Result of processing one receipt: state, new receipts, outcomes, and the
yocto paid to contracts as gas reward (which are not burnt). -/
structure Processed where
  storageAccounting : Option TrieOverlay.State := none
  state : ChainState
  receipts : List Receipt := []
  identityBirths : List ReceiptIdentityBirth := []
  outcomes : List (ReceiptId × ExecutionOutcome) := []
  subsidizedAmount : Nat := 0
  rewards : Nat := 0
  otherTokensBurnt : Nat := 0
  /-- Compute that is not gas: applying a global contract distribution. -/
  extraCompute : Nat := 0
  issue : Option (ReceiptId × ExecutionIssue) := none
  deriving Inhabited

/-- Whether a receipt runs in the chunk that creates it instead of travelling as an outgoing
receipt (`Receipt::is_instant_receipt`): a yield, or a lone account deletion with no inputs. -/
def Receipt.isInstant (r : Receipt) : Bool :=
  match r.receipt with
  | .action a =>
    a.yieldDataId.isSome || (a.inputDataIds.isEmpty && match a.actions with
      | [.deleteAccount _] => true
      | _ => false)
  | _ => false

/-- The data ids of the yields an account has outstanding. -/
def yieldsOf (st : ChainState) (account : AccountId) : List Bytes :=
  (st.yieldReceipts.filter (·.1.1 == account)).map (·.1.2) ++ (st.yieldStatus.filter (·.1.1 == account)).map (·.1.2)

/-- An action receipt whose inputs have all arrived, executed with the given promise results. -/
def runActionReceipt (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (r : Receipt) (a : ActionReceipt) (results : List PromiseResult) : Processed :=
  let ctx : ReceiptCtx :=
    { cfg, ap, receipt := r, action := a, promiseResults := results, codeOf, vmYields := yieldsOf st r.receiverId }
  let e := applyActionReceipt ctx st
  let issue := match e.result with
    | some (.failure error) => error.issue?
    | _ => none
  match issue with
  | some issue => { state := st, issue := some (r.receiptId, issue) }
  | none =>
    { storageAccounting := e.storageAccounting, state := e.state, receipts := e.newReceipts,
      identityBirths := [{ parent := r.receiptId, children := e.newReceipts.map (·.receiptId), vmActions := e.vmIdentityBirths }],
      outcomes := [(r.receiptId, outcomeOf r e)],
      rewards := e.reward, otherTokensBurnt := e.otherTokensBurnt, subsidizedAmount := e.subsidizedAmount }

/-- `apply_global_contract_distribution_receipt`: register the code unless a newer distribution
already did, then pass the receipt on to the next shard that has not seen it. -/
def processDistribution (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) : Processed :=
  let fresh := !cfg.globalContractDistributionNonce || g.nonce ≥ st.globalNonce g.id
  let st := if fresh then
      let st := if cfg.globalContractDistributionNonce then st.setGlobalNonce g.id g.nonce else st
      st.setGlobalCode g.id g.code
    else st
  let compute := if fresh then cfg.deployGlobalContractExecutionBase
      + cfg.deployGlobalContractExecutionPerByte * g.code.size else 0
  let delivered := (g.alreadyDelivered ++ [ap.shardId]).eraseDups.mergeSort
  match ap.shardIds.find? (fun shard => !delivered.contains shard) with
  | none => { state := st, storageAccounting := ap.storageAccounting, extraCompute := compute }
  | some next =>
    let (rid, st) := st.freshId
    let forwarded : Receipt :=
      { predecessorId := r.predecessorId, receiverId := r.receiverId, receiptId := rid
        receipt := .globalDistribution { g with targetShard := next, alreadyDelivered := delivered } }
    { state := st, storageAccounting := ap.storageAccounting, extraCompute := compute,
      receipts := [forwarded],
      identityBirths := [{ parent := r.receiptId, children := [rid], vmActions := [] }] }

/-- One receipt: action receipts run (or wait for data), data receipts feed
the receipt waiting for them. Returns the outcomes of everything that ran. -/
def processReceipt (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (r : Receipt) : Processed :=
  match r.receipt with
  | .action a =>
    match a.yieldDataId with
    | some dataId =>
      -- A yield only waits, stored until its data or its timeout arrives.
      -- nearcore divergence: a data id that is already waiting would be overwritten in the trie;
      -- hashes make that unreachable, and the model reports it instead of losing the funds.
      if (Assoc.lookup st.yieldReceipts (r.receiverId, dataId)).isSome then
        { state := st, storageAccounting := ap.storageAccounting
          issue := some (r.receiptId, .unsupportedAction "duplicate yielded data id") }
      else
        { state := { st with yieldReceipts := Assoc.insert st.yieldReceipts (r.receiverId, dataId) r },
          storageAccounting := ap.storageAccounting }
    | none =>
    let missing := a.inputDataIds.filter fun d => !(Assoc.contains st.receivedData d)
    if missing.isEmpty then
      let results := a.inputDataIds.map fun d =>
        match Assoc.lookup st.receivedData d with
        | some (some bytes) => PromiseResult.successful bytes
        | _ => PromiseResult.failed
      let st := { st with receivedData := st.receivedData.filter fun (d, _) => !a.inputDataIds.contains d }
      runActionReceipt cfg ap codeOf st r a results
    else
      let st := { st with
        postponed := Assoc.insert st.postponed r.receiptId r
        pendingDataCount := Assoc.insert st.pendingDataCount r.receiptId missing.length
        postponedByData := missing.foldl (fun m d => Assoc.insert m d r.receiptId) st.postponedByData }
      { state := st, storageAccounting := ap.storageAccounting }
  | .globalDistribution g => processDistribution cfg ap st r g
  | .data d =>
    match d.resumeDataId with
    | some dataId =>
      let key := (r.receiverId, dataId)
      if d.data.isNone && Assoc.lookup st.yieldStatus key == some YieldStatus.resumeInitiated then
        -- A resume has been sent: the timeout is moot.
        { state := st, storageAccounting := ap.storageAccounting }
      else
        match Assoc.lookup st.yieldReceipts key with
        | some y =>
          let st := { st with yieldReceipts := Assoc.erase st.yieldReceipts key
                              yieldStatus := Assoc.erase st.yieldStatus key }
          match y.receipt with
          | .action a =>
            let result := match d.data with
              | some bytes => PromiseResult.successful bytes
              | none => PromiseResult.failed
            runActionReceipt cfg ap codeOf st y a [result]
          | _ => { state := st, storageAccounting := ap.storageAccounting }
        | none => { state := st, storageAccounting := ap.storageAccounting }
    | none =>
    match Assoc.lookup st.postponedByData d.dataId with
    | some rid =>
      let st := { st with
        receivedData := Assoc.insert st.receivedData d.dataId d.data
        postponedByData := Assoc.erase st.postponedByData d.dataId }
      let pending := (Assoc.lookup st.pendingDataCount rid).getD 1 - 1
      if pending == 0 then
        match _found : Assoc.lookup st.postponed rid with
        | some waiting =>
          let st := { st with postponed := Assoc.erase st.postponed rid
                              pendingDataCount := Assoc.erase st.pendingDataCount rid }
          processReceipt cfg ap codeOf st waiting
        | none => { state := st, storageAccounting := ap.storageAccounting }
      else { state := { st with pendingDataCount := Assoc.insert st.pendingDataCount rid pending }, storageAccounting := ap.storageAccounting }
    | none => { state := { st with receivedData := Assoc.insert st.receivedData d.dataId d.data }, storageAccounting := ap.storageAccounting }
termination_by st.postponed.length
decreasing_by
  exact Assoc.erase_length_lt_of_lookup _ _ _ _found

/-- What was processed after `p`, appended to it (the later state wins). -/
def Processed.append (p q : Processed) : Processed :=
  { storageAccounting := q.storageAccounting, state := q.state
    receipts := p.receipts ++ q.receipts
    identityBirths := p.identityBirths ++ q.identityBirths
    outcomes := p.outcomes ++ q.outcomes
    subsidizedAmount := p.subsidizedAmount + q.subsidizedAmount
    rewards := p.rewards + q.rewards
    otherTokensBurnt := p.otherTokensBurnt + q.otherTokensBurnt
    extraCompute := p.extraCompute + q.extraCompute
    issue := p.issue.orElse fun _ => q.issue }

/-- The receipt shapes the funding theory covers: a system refund is one transfer, every other
receipt names neither the system account as receiver nor as signer. -/
def Receipt.fundedShape (r : Receipt) : Bool :=
  match r.receipt with
  | .action a =>
    if r.predecessorId == systemAccount then
      match a.actions with
      | [.transfer _] => true
      | _ => false
    else r.receiverId != systemAccount && a.signerId != systemAccount
  | .data _ | .globalDistribution _ => true

/-- The instant receipts a processed receipt created run right after it, in creation order,
and are not sent out (`process_receipt_and_instant_receipts`).
nearcore divergence: an instant receipt outside `Receipt.fundedShape`, in practice one addressed to
the `system` account, is reported as unsupported instead of executed. -/
def processInstants (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode) :
    Nat → Processed → List Receipt → Processed
  | _, acc, [] => acc
  | 0, acc, r :: _ =>
    { acc with issue := some (r.receiptId, .interpreterError "instant receipts did not settle") }
  | fuel + 1, acc, r :: rest =>
    if !r.fundedShape then
      { acc with issue := some (r.receiptId, .unsupportedAction "instant receipt addressed to the system account") }
    else
    let p := processReceipt cfg { ap with storageAccounting := acc.storageAccounting } codeOf acc.state r
    if p.issue.isSome then { acc with issue := p.issue } else
    let instant := p.receipts.filter Receipt.isInstant
    processInstants cfg ap codeOf fuel
      (acc.append { p with receipts := p.receipts.filter fun x => !x.isInstant }) (rest ++ instant)

/-- A receipt together with the instant receipts it creates. -/
def processWithInstants (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (r : Receipt) : Processed :=
  let p := processReceipt cfg ap codeOf st r
  if p.issue.isSome then p else
  processInstants cfg ap codeOf 1024 { p with receipts := p.receipts.filter fun x => !x.isInstant }
    (p.receipts.filter Receipt.isInstant)

/-- `resolve_promise_yield_timeouts`: yields whose time has come are woken with a timeout
resume, in queue order, until the chunk's budget is spent. -/
def resolveYieldTimeouts (ap : ApplyState) (limit : Option Nat) (used : Nat) :
    Nat → ChainState × List Receipt × List ReceiptIdentityBirth →
      ChainState × List Receipt × List ReceiptIdentityBirth
  | 0, acc => acc
  | fuel + 1, (st, receipts, births) =>
    match st.yieldIndices with
    | none => (st, receipts, births)
    | some (first, next) =>
      if first < next && !(limit.any (used ≥ ·)) then
        match Assoc.lookup st.yieldTimeouts first with
        | none => (st, receipts, births)
        | some entry =>
          if entry.expiresAt > ap.blockHeight then (st, receipts, births) else
          let key := (entry.account, entry.dataId)
          let st := { st with yieldTimeouts := Assoc.erase st.yieldTimeouts first
                              yieldIndices := some (first + 1, next) }
          if (Assoc.lookup st.yieldReceipts key).isSome then
            let (rid, st) := st.freshId
            let resume : Receipt :=
              { predecessorId := entry.account, receiverId := entry.account, receiptId := rid
                receipt := .data { dataId := 0, data := none, resumeDataId := some entry.dataId } }
            let birth : ReceiptIdentityBirth :=
              { parent := 0, children := [rid], vmActions := [],
                parentHash := some entry.dataId, startIndex := receipts.length }
            resolveYieldTimeouts ap limit used fuel (st, receipts ++ [resume], births ++ [birth])
          else resolveYieldTimeouts ap limit used fuel (st, receipts, births)
      else (st, receipts, births)

/-! ## Transactions -/

/-- Access-key authorization and allowance debit before a transaction commits. -/
def validateTransactionAccessKey (tx : Transaction) (key : AccessKey) (cost : Fees.TxCost) :
    Except RuntimeError AccessKey := do
  match key.permission with
    | .fullAccess => pure { key with nonce := tx.nonce }
    | .functionCall allowance receiver methods =>
      match tx.actions with
      | [.functionCall m _ _ deposit] =>
        if deposit > 0 then throw (.invalidAccessKey "DepositWithFunctionCall")
        if tx.receiverId != receiver then throw (.receiverMismatch tx.receiverId receiver)
        if !(methods.isEmpty || methods.contains m) then throw (.methodNameMismatch m)
        match allowance with
        | some al =>
          if al < cost.total then throw (.notEnoughAllowance tx.signerId tx.publicKey al cost.total)
          pure { nonce := tx.nonce, permission := .functionCall (some (al - cost.total)) receiver methods }
        | none => pure { key with nonce := tx.nonce }
      | _ => throw (.invalidAccessKey "RequiresFullAccess")
    | .gasKeyFullAccess .. | .gasKeyFunctionCall .. =>
      -- nearcore divergence: transactions signed by a gas key pay from the key's balance and
      -- advance one of its nonce lanes; the model rejects them as unsupported.
      throw (.executionIssue (.unsupportedAction "transaction signed by a gas key"))

/-- Native admission checks finite allowance before storage stake and permissions. -/
def validateTransactionAllowance (tx : Transaction) (key : AccessKey) (cost : Fees.TxCost) :
    Except RuntimeError Unit := do
  if let .functionCall (some allowance) _ _ := key.permission then
    if allowance < cost.total then
      throw (.notEnoughAllowance tx.signerId tx.publicKey allowance cost.total)

/-- Commit the already-validated transaction debit, key update and fresh receipt.
Callers must establish that `signer` is the current signer account and funded. -/
def commitTransaction (st : ChainState) (tx : Transaction) (signer : Account)
    (newKey : AccessKey) (cost : Fees.TxCost) : ChainState × Receipt × Fees.TxCost :=
  let st := (st.setAccount tx.signerId { signer with amount := signer.amount - cost.total }).setAccessKey
    tx.signerId tx.publicKey newKey
  let (id, st) := st.freshId
  let action : ActionReceipt :=
    { signerId := tx.signerId
      signerPublicKey := tx.publicKey
      gasPrice := cost.receiptGasPrice
      actions := tx.actions }
  let receipt : Receipt :=
    { predecessorId := tx.signerId
      receiverId := tx.receiverId
      receiptId := id
      receipt := .action action }
  (st, receipt, cost)

/-- `verify_and_charge_transaction`: signer, key, nonce, permission and
balance checks; charges the cost; bumps the nonce; returns the receipt. -/
def convertTransactionCore (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (tx : Transaction) :
    Except RuntimeError (ChainState × Receipt × Fees.TxCost) := do
  if tx.nonceMode = .strict ∧ cfg.strictNonceEnabled = false then throw .invalidTransactionVersion
  if tx.versionSupported cfg = false then throw .invalidTransactionVersion
  let some size := tx.sizeForLimits? cfg
    | throw (.executionIssue (.unsupportedAction "transaction signature/key encoding"))
  if size > cfg.wasm.limits.maxTransactionSize then
    throw (.transactionSizeExceeded size cfg.wasm.limits.maxTransactionSize)
  let some signer := st.account? tx.signerId | throw (.invalidSigner tx.signerId)
  let some key := st.accessKey? tx.signerId tx.publicKey | throw (.accessKeyNotFound tx.signerId tx.publicKey)
  verifyNonce tx.nonce key.nonce (some ap.blockHeight) tx.nonceMode
  if tx.actions.length > cfg.wasm.limits.maxActionsPerReceipt then
    throw (.tooManyActions tx.actions.length cfg.wasm.limits.maxActionsPerReceipt)
  let cost := Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions
  if signer.amount < cost.total then throw (.notEnoughBalance tx.signerId signer.amount cost.total)
  validateTransactionAllowance tx key cost
  let signer' := { signer with amount := signer.amount - cost.total }
  let deficit := storageStakeDeficit cfg signer'
  if deficit > 0 then throw (.lackBalanceForState tx.signerId deficit)
  let key' ← validateTransactionAccessKey tx key cost
  return commitTransaction st tx signer key' cost

/-- Stateless actions are checked before envelope/key admission or any charge. -/
def convertTransaction (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (tx : Transaction) :
    Except RuntimeError (ChainState × Receipt × Fees.TxCost) := do
  match validateTransactionActions cfg tx.actions with
  | .error error => throw (.actionsValidation error)
  | .ok () => convertTransactionCore cfg ap st tx

-- nearcore divergence: one shard; no congestion-control buffering, bandwidth scheduler,
-- epoch validator-account updates or incoming-receipt validation (`Runtime::apply`,
-- `process_receipts`). Instant receipts and yield timeouts are modelled.
/-- `Runtime::apply`. Transactions first; only signer-is-receiver receipts
are local. Other transaction receipts are outgoing work for a later chunk.
Local, delayed and incoming receipts execute in that order; receipts beyond
the gas limit are delayed to the next apply. -/
def applyAttempt (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) : ApplyResult := Id.run do
  let initial := st
  let mut st := st
  let mut outcomes : List (ReceiptId × ExecutionOutcome) := []
  let mut outgoing : List Receipt := []
  let mut localReceipts : List Receipt := []
  let mut identityBirths : List ReceiptIdentityBirth := []
  let mut subsidizedAmount := 0
  let mut tokensBurnt := 0
  let mut txIndex := 0
  for tx in txs do
    txIndex := txIndex + 1
    match convertTransaction cfg ap st tx with
    | .ok (st', r, cost) =>
      st := st'
      if tx.signerId == tx.receiverId then
        localReceipts := localReceipts ++ [r]
      else
        outgoing := outgoing ++ [r]
      tokensBurnt := tokensBurnt + cost.gasBurnt * ap.gasPrice
      let o : ExecutionOutcome :=
        { executorId := tx.signerId
          status := .successReceiptId r.receiptId
          receiptIds := [r.receiptId]
          gasBurnt := cost.gasBurnt
          tokensBurnt := cost.gasBurnt * ap.gasPrice }
      outcomes := outcomes ++ [(0, o)]
    | .error e =>
      if let some issue := e.issue? then
        return { state := initial, outgoing := [], outcomes := [], tokensBurnt := 0, issue := some (0, issue) }
      outcomes := outcomes ++ [(0, { executorId := tx.signerId, status := .failure e })]
  let delayedStart := localReceipts.length
  let delayedEnd := delayedStart + st.delayed.length
  let queue := localReceipts ++ st.delayed ++ incoming
  st := { st with delayed := [] }
  let mut retainedDelayed : List Receipt := []
  let mut newlyDelayed : List Receipt := []
  let mut gasUsed := outcomes.foldl (fun total pair => total + pair.2.gasBurnt) 0
  let mut overLimit := ap.gasLimit.any (gasUsed ≥ ·)
  let mut storageAccounting := ap.storageAccounting
  for (r, position) in queue.zipIdx do
    if overLimit then
      -- Local execution has priority, but new deferrals append to the existing
      -- persistent queue. Untouched old entries retain their FIFO positions.
      if delayedStart ≤ position && position < delayedEnd then
        retainedDelayed := retainedDelayed ++ [r]
      else
        newlyDelayed := newlyDelayed ++ [r]
    else
      let p := processWithInstants cfg { ap with storageAccounting } codeOf st r
      storageAccounting := p.storageAccounting
      if let some issue := p.issue then
        return { state := initial, outgoing := [], outcomes := [], tokensBurnt := 0, issue := some issue }
      identityBirths := identityBirths ++ p.identityBirths
      subsidizedAmount := subsidizedAmount + p.subsidizedAmount
      st := p.state
      outgoing := outgoing ++ p.receipts
      outcomes := outcomes ++ p.outcomes
      for (_, o) in p.outcomes do
        gasUsed := gasUsed + o.gasBurnt
        tokensBurnt := tokensBurnt + o.tokensBurnt
      gasUsed := gasUsed + p.extraCompute
      tokensBurnt := tokensBurnt + p.otherTokensBurnt - p.rewards
      if let some limit := ap.gasLimit then
        if gasUsed ≥ limit then overLimit := true
  -- Yields that timed out wake up with a resume receipt, after all incoming receipts.
  let (stTimed, timeoutReceipts, timeoutBirths) := resolveYieldTimeouts ap ap.gasLimit gasUsed
    (st.yieldTimeouts.length + 1) (st, [], [])
  st := stTimed
  outgoing := outgoing ++ timeoutReceipts
  identityBirths := identityBirths ++ timeoutBirths
  return {
    state := { st with delayed := retainedDelayed ++ newlyDelayed }, outgoing, outcomes, tokensBurnt, subsidizedAmount, identityBirths
    storageAccounting
    proposals := outcomes.flatMap (·.2.proposals)
    delayedConsumed := initial.delayed.length - retainedDelayed.length, delayedAppended := newlyDelayed.length }

/-- Commit a supported chunk. Model limitations invalidate the entire attempt:
no fees, refunds, nonces, receipt consumption, or state changes are committed. -/
def apply (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) : ApplyResult :=
  let result := applyAttempt cfg ap codeOf st txs incoming
  if result.issue.isSome then
    { result with state := st, outgoing := [], outcomes := [], tokensBurnt := 0, subsidizedAmount := 0, proposals := [], identityBirths := [], delayedConsumed := 0, delayedAppended := 0 }
  else result

/-- The proposals `ApplyResult::validator_proposals` carries: one per account, the last one the
chunk made, in the reverse of the order they were made in (`Runtime::apply` walks the proposals
backwards and keeps the first it meets of each account). -/
def uniqueProposals (proposals : List ValidatorProposal) : List ValidatorProposal :=
  proposals.reverse.foldl (fun kept p =>
    if kept.any (·.account == p.account) then kept else kept ++ [p]) []

/-- An unsupported or incomplete apply is atomic with respect to all public
protocol observations, including work that preceded the problematic receipt. -/
theorem apply_issue_atomic (cfg : RuntimeConfig) (ap : ApplyState)
    (codeOf : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : (apply cfg ap codeOf st txs incoming).issue ≠ none) :
    (apply cfg ap codeOf st txs incoming).state = st ∧
    (apply cfg ap codeOf st txs incoming).outgoing = [] ∧
    (apply cfg ap codeOf st txs incoming).outcomes = [] ∧
    (apply cfg ap codeOf st txs incoming).tokensBurnt = 0 := by
  cases hi : (applyAttempt cfg ap codeOf st txs incoming).issue with
  | none => simp [apply, hi] at h
  | some issue => simp [apply, hi]

/-- A model issue never commits attempted minting. -/
theorem apply_issue_subsidized_zero (cfg : RuntimeConfig) (ap : ApplyState)
    (codeOf : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : (apply cfg ap codeOf st txs incoming).issue ≠ none) :
    (apply cfg ap codeOf st txs incoming).subsidizedAmount = 0 := by
  cases hi : (applyAttempt cfg ap codeOf st txs incoming).issue with
  | none => simp [apply, hi] at h
  | some issue => simp [apply, hi]

end Near
