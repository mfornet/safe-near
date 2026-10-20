import NearRuntime.Fees
import NearRuntime.State
import NearRuntime.Nonce
import NearRuntime.Refund
import NearRuntime.ActionValidation
import NearRuntime.TransactionSize
import NearRuntime.NativeIdentity

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
  deriving Inhabited

/-- Final child order includes refunds and completion data. VM origins only
survive successful receipt execution; rollback discards their allocations. -/
structure ReceiptIdentityBirth where
  parent : ReceiptId
  children : List ReceiptId
  vmActions : List VMIdentityBirth
  deriving Inhabited

structure ApplyResult where
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
  /-- No state transition is committed when the model cannot execute a receipt.
  The state is the input state and the protocol observations are empty. -/
  issue : Option (ReceiptId × ExecutionIssue) := none

/-! ## Execution monad -/

/-- State threaded through one receipt: the chain state, the receipts and
outcomes produced so far, and the gas accounting of the receipt. -/
structure Exec where
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
  /-- Failed system refunds burn their deposit outside the execution outcome. -/
  otherTokensBurnt : Nat := 0
  /-- Yocto credited to the contract out of its burnt gas (`burnt_gas_reward`). -/
  reward : Nat := 0
  logs : List String := []
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
    .addKey pk { nonce := nonce.toNat, permission }
  | .deleteKey pk => .deleteKey pk
  | .deleteAccount beneficiary => .deleteAccount (stringOfBytes beneficiary)

/-- Missing external decoders are model issues, never silently deployable code. -/
def actionOfPromise (codeOf : Bytes → ContractCode) (action : PromiseAction) : Except RuntimeError Action := do
  let converted := actionOfPromiseRaw codeOf action
  if let .deployContract code := converted then
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
  /-- Decoder for code deployed by contracts (not available in Lean yet). -/
  codeOf : Bytes → ContractCode

/-- Exact VM context used by a receipt function-call action. -/
def functionCallContext (c : ReceiptCtx) (account : Account) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) : VMContext :=
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
    chargeStorageValueAccess := true
    outputDataReceivers := if isLast then c.action.outputDataReceivers.map fun d => bytesOfString d.receiverId else [] }

/-- Gas/log observations from one VM call, before its success/failure branch. -/
def Exec.recordVMOutcome (exec : Exec) (outcome : VMOutcome) : Exec :=
  { exec with
    logs := exec.logs ++ outcome.logs
    gasBurntForFunctionCall := exec.gasBurntForFunctionCall + outcome.burntGas
    gasBurnt := exec.gasBurnt + outcome.burntGas
    gasUsed := exec.gasUsed + outcome.burntGas + (outcome.usedGas - outcome.burntGas) }

structure FunctionCallEffects where
  state : ChainState
  receipts : List Receipt
  result : ExecutionStatus

/-- Materialize the VM's ordered receipts and data dependencies without touching
execution gas. Id allocation and outgoing order match receipt execution. -/
def materializeFunctionCallRaw (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
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
  let outputReceivers := if isLast then c.action.outputDataReceivers else []
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
        actions := actions } }]
  return { state := st, receipts, result }

/-- The entire promise set is checked before pure construction/commit. -/
def validateFunctionCallActions (c : ReceiptCtx) (outcome : VMOutcome) : Except RuntimeError Unit := do
  for spec in outcome.receipts do
    let _ ← spec.actions.mapM (actionOfPromise c.codeOf)
  pure ()

def materializeFunctionCall (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) : Except RuntimeError FunctionCallEffects := do
  validateFunctionCallActions c outcome
  return materializeFunctionCallRaw c isLast outcome initial

/-- A successful checked construction is exactly the pure stage, with no fallback actions. -/
theorem materializeFunctionCall_success (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (effects : FunctionCallEffects)
    (h : materializeFunctionCall c isLast outcome initial = .ok effects) :
    effects = materializeFunctionCallRaw c isLast outcome initial := by
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
        | .data _ => []
        | .action action => action.inputDataIds.map (·, receipt.receiverId) }]
    result := some effects.result
    subsidizedAmount := exec.subsidizedAmount + outcome.subsidizedAmount }

/-- Validate promised actions and materialize successful state changes before commit. -/
def functionCallEffects (c : ReceiptCtx) (account : Account) (outcome : VMOutcome)
    (isLast : Bool) (state : ChainState) : Except RuntimeError FunctionCallEffects :=
  let id := c.receipt.receiverId
  let state := state.setAccount id { account with amount := outcome.balance, storageUsage := outcome.storageUsage }
  let state := state.setContractStorage id outcome.storage
  materializeFunctionCall c isLast outcome state

/-- Execute a function call and turn its promises into receipts. -/
def applyFunctionCall (c : ReceiptCtx) (method : String) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) : ExecM Unit := do
  let account ← getAccount c.receipt.receiverId
  let some code := account.code
    | throw (.functionCallError (.compilationError "CodeDoesNotExist"))
  if let some issue := code.decodeIssue then throw (.executionIssue issue)
  let st ← getState
  let ctx := functionCallContext c account args gas deposit isLast
  let outcome := run c.cfg code.module code.size method ctx (st.contractStorage c.receipt.receiverId)
  modify (·.recordVMOutcome outcome)
  match outcome.aborted with
  | some err => throw (.functionCallError err)
  | none =>
    match functionCallEffects c account outcome isLast st with
    | .error error => throw error
    | .ok effects => modify (·.commitFunctionCall outcome effects)

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
    let old := (a.code.map (·.size)).getD 0
    putAccount id { a with code := some code, storageUsage := a.storageUsage + code.size - old }
  | .functionCall m args gas deposit => applyFunctionCall c m args gas deposit isLast
  | .transfer deposit => do
    let id := c.receipt.receiverId
    match (← getState).account? id with
    | some a => do
      putAccount id { a with amount := a.amount + deposit }
      if c.receipt.isGasRefund then
        modifyState (·.refundAllowance id c.action.signerPublicKey deposit)
    | none =>
      if unsupportedImplicitCreation c.cfg.wasm.ethImplicitAccounts (bytesOfString id) then
        throw (.executionIssue (.unsupportedAction "implicit account creation (ETH/deterministic contracts)"))
      -- implicit account creation on transfer
      if let some pk := implicitPublicKey? id then
        let key : AccessKey := { nonce := initialNonce c.ap.blockHeight, permission := .fullAccess }
        putAccount id { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount
          + accessKeyStorageBytes pk key
          + c.cfg.fees.numExtraBytesRecord }
        modifyState (·.setAccessKey id pk key)
        modify fun e => { e with actorId := id }
      else throw (.accountDoesNotExist id)
  | .stake stake pk => do
    let id := c.receipt.receiverId
    let a ← getAccount id
    let _ := pk
    if stake == 0 && a.locked == 0 then throw (.triesToUnstake id)
    if stake > a.amount + a.locked then throw (.triesToStake id stake a.locked a.amount)
    if stake < a.locked then
      throw (.executionIssue (.unsupportedAction "unstake (epoch machinery)"))
    -- Staking also emits validator proposals and depends on epoch-provider
    -- eligibility checks. A local balance update would fabricate success.
    throw (.executionIssue (.unsupportedAction "stake (epoch machinery)"))
  | .addKey pk key => do
    let id := c.receipt.receiverId
    let st ← getState
    if (st.accessKey? id pk).isSome then throw (.addKeyAlreadyExists id pk)
    let a ← getAccount id
    putAccount id { a with storageUsage := a.storageUsage + accessKeyStorageBytes pk key
      + c.cfg.fees.numExtraBytesRecord }
    modifyState (·.setAccessKey id pk { key with nonce := initialNonce c.ap.blockHeight })
  | .deleteKey pk => do
    let id := c.receipt.receiverId
    let st ← getState
    let some key := st.accessKey? id pk | throw (.deleteKeyDoesNotExist id pk)
    let a ← getAccount id
    putAccount id { a with storageUsage := a.storageUsage - (accessKeyStorageBytes pk key
      + c.cfg.fees.numExtraBytesRecord) }
    modifyState (·.removeAccessKey id pk)
  | .deleteAccount beneficiary => do
    let id := c.receipt.receiverId
    unless isLast do throw .deleteActionMustBeFinal
    let a ← getAccount id
    if a.locked > 0 then throw (.deleteAccountStaking id)
    let st ← getState
    let (r, st) := refundReceipt st beneficiary a.amount
    modify fun exec => { exec with state := st.removeAccount id }
    modify fun e => { e with actorId := c.receipt.predecessorId }
    emit r

/-- Pinned nearcore verifier's zero-balance account exemption (NEP-448). -/
def zeroBalanceAccountStorageLimit : Nat := 770

def storageStakeDeficit (cfg : RuntimeConfig) (a : Account) : Nat :=
  if a.storageUsage ≤ zeroBalanceAccountStorageLimit then 0
  else a.storageUsage * cfg.storageAmountPerByte - a.amount - a.locked

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
  | .deployContract _ | .stake .. | .addKey .. | .deleteKey _ | .deleteAccount _ =>
    if actor == receiver then .ok () else .error (.actorNoPermission receiver actor)
  | _ => .ok ()

def Action.requiresActor : Action → Bool
  | .deployContract _ | .stake .. | .addKey .. | .deleteKey _ | .deleteAccount _ => true
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

/-- Derivation is local to one call: later actions still start from the block
seed, while non-VM actions need no random context. Invalid exact-mode context
is a model issue and rolls back the chunk rather than failing a contract. -/
def runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool) (act : Action) (index : Nat) : ExecM Unit :=
  match act with
  | .functionCall .. =>
    match actionRandomSeed c index with
    | .error error => throw (.executionIssue (.interpreterError s!"Native action randomness context: {error}"))
    | .ok seed => runReceiptAction { c with vmRandomSeed := some seed } onlyAction isLast act
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
  let exec0 : Exec := { state := st0, actorId := c.receipt.predecessorId }
  match ((receiptActionBody c).run.run exec0) with
    | (.ok (), e) => (e, none)
    | (.error err, e) => (e, some err)

/-- Receipt failure restores the pre-action state while retaining gas and logs. -/
def rollbackReceipt (st0 : ChainState) (exec : Exec) (failed : Option RuntimeError) : Exec :=
  match failed with
    | some err => { exec with state := st0, newReceipts := [], vmIdentityBirths := [], subsidizedAmount := 0, gasUsed := exec.gasBurnt,
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

/-- Completed data follows refunds. Returning a promise delegates these
outputs to that promise; other completions carry their value or failure. -/
def completionDataStep (receiver : AccountId) (data : Option Bytes)
    (acc : ChainState × List Receipt) (d : DataReceiver) : ChainState × List Receipt :=
  let (st, rs) := acc
  let (id, st) := st.freshId
  (st, rs ++ [{
    predecessorId := receiver
    receiverId := d.receiverId
    receiptId := id
    receipt := .data { dataId := d.dataId, data := data } }])

def Exec.addCompletionData (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) : Exec :=
  let result := match exec.result with
    | some (.successReceiptId _) => none
    | some (.failure _) => some none
    | some (.successValue value) => some (some value)
    | none => some (some [])
  match result with
  | none => exec
  | some data =>
    let (st, rs) := outputs.foldl (completionDataStep receiver data) (exec.state, [])
    { exec with state := st, newReceipts := exec.newReceipts ++ rs }

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
    tokensBurnt := if isRefund then 0 else settlement.tokensBurnt
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
  let exec := if failed.isSome then exec.addFailureData receiver c.action.outputDataReceivers
    else exec.addCompletionData receiver c.action.outputDataReceivers
  { exec with result := some (exec.result.getD (.successValue [])) }


/-- Execute and finalize the actual action receipt. -/
def applyActionReceipt (c : ReceiptCtx) (st0 : ChainState) : Exec :=
  let (exec, failed) := runReceiptActions c st0
  finalizeReceipt c st0 exec failed

/-- Outcome of an executed receipt. -/
def outcomeOf (r : Receipt) (e : Exec) : ExecutionOutcome :=
  { failureIndex := e.failureIndex
    executorId := r.receiverId
    status := e.result.getD (.successValue [])
    logs := e.logs
    receiptIds := (e.newReceipts.filter fun r => match r.receipt with
      | .action _ => true
      | .data _ => false).map (·.receiptId)
    gasBurnt := e.gasBurnt
    tokensBurnt := e.tokensBurnt }

/-- Result of processing one receipt: state, new receipts, outcomes, and the
yocto paid to contracts as gas reward (which are not burnt). -/
structure Processed where
  state : ChainState
  receipts : List Receipt := []
  identityBirths : List ReceiptIdentityBirth := []
  outcomes : List (ReceiptId × ExecutionOutcome) := []
  subsidizedAmount : Nat := 0
  rewards : Nat := 0
  otherTokensBurnt : Nat := 0
  issue : Option (ReceiptId × ExecutionIssue) := none
  deriving Inhabited

/-- One receipt: action receipts run (or wait for data), data receipts feed
the receipt waiting for them. Returns the outcomes of everything that ran. -/
def processReceipt (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (r : Receipt) : Processed :=
  match r.receipt with
  | .action a =>
    let missing := a.inputDataIds.filter fun d => !(Assoc.contains st.receivedData d)
    if missing.isEmpty then
      let results := a.inputDataIds.map fun d =>
        match Assoc.lookup st.receivedData d with
        | some (some bytes) => PromiseResult.successful bytes
        | _ => PromiseResult.failed
      let st := { st with receivedData := st.receivedData.filter fun (d, _) => !a.inputDataIds.contains d }
      let e := applyActionReceipt { cfg, ap, receipt := r, action := a, promiseResults := results, codeOf } st
      let issue := match e.result with
        | some (.failure error) => error.issue?
        | _ => none
      match issue with
      | some issue => { state := st, issue := some (r.receiptId, issue) }
      | none =>
        { state := e.state, receipts := e.newReceipts,
          identityBirths := [{ parent := r.receiptId, children := e.newReceipts.map (·.receiptId), vmActions := e.vmIdentityBirths }],
          outcomes := [(r.receiptId, outcomeOf r e)],
          rewards := e.reward, otherTokensBurnt := e.otherTokensBurnt, subsidizedAmount := e.subsidizedAmount }
    else
      let st := { st with
        postponed := Assoc.insert st.postponed r.receiptId r
        pendingDataCount := Assoc.insert st.pendingDataCount r.receiptId missing.length
        postponedByData := missing.foldl (fun m d => Assoc.insert m d r.receiptId) st.postponedByData }
      { state := st }
  | .data d =>
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
        | none => { state := st }
      else { state := { st with pendingDataCount := Assoc.insert st.pendingDataCount rid pending } }
    | none => { state := { st with receivedData := Assoc.insert st.receivedData d.dataId d.data } }
termination_by st.postponed.length
decreasing_by
  exact Assoc.erase_length_lt_of_lookup _ _ _ _found

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
  for (r, position) in queue.zipIdx do
    if overLimit then
      -- Local execution has priority, but new deferrals append to the existing
      -- persistent queue. Untouched old entries retain their FIFO positions.
      if delayedStart ≤ position && position < delayedEnd then
        retainedDelayed := retainedDelayed ++ [r]
      else
        newlyDelayed := newlyDelayed ++ [r]
    else
      let p := processReceipt cfg ap codeOf st r
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
      tokensBurnt := tokensBurnt + p.otherTokensBurnt - p.rewards
      if let some limit := ap.gasLimit then
        if gasUsed ≥ limit then overLimit := true
  return {
    state := { st with delayed := retainedDelayed ++ newlyDelayed }, outgoing, outcomes, tokensBurnt, subsidizedAmount, identityBirths
    delayedConsumed := initial.delayed.length - retainedDelayed.length, delayedAppended := newlyDelayed.length }

/-- Commit a supported chunk. Model limitations invalidate the entire attempt:
no fees, refunds, nonces, receipt consumption, or state changes are committed. -/
def apply (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) : ApplyResult :=
  let result := applyAttempt cfg ap codeOf st txs incoming
  if result.issue.isSome then
    { result with state := st, outgoing := [], outcomes := [], tokensBurnt := 0, subsidizedAmount := 0, identityBirths := [], delayedConsumed := 0, delayedAppended := 0 }
  else result

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
