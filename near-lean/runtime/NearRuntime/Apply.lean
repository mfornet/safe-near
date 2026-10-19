import NearRuntime.Fees
import NearRuntime.State

/-!
# `apply`

`runtime/src/lib.rs`: transactions become receipts, receipts execute their
actions, failures roll back and refund, data receipts resolve callbacks,
and everything that happens is reported as an `ExecutionOutcome`.
-/

namespace Near

open Wasm Wasm.Near

structure ApplyResult where
  state : ChainState
  outgoing : List Receipt
  /-- One outcome per transaction and per processed receipt, in order. -/
  outcomes : List (ReceiptId × ExecutionOutcome)
  /-- Yocto burnt as gas during this apply: gas × price of every outcome,
  minus what went to contracts as `burnt_gas_reward`. -/
  tokensBurnt : Nat
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
  newReceipts : List Receipt := []
  gasBurnt : Nat := 0
  /-- Gas burnt or attached onward; what is left of the receipt's gas is refunded. -/
  gasUsed : Nat := 0
  gasBurntForFunctionCall : Nat := 0
  /-- Yocto credited to the contract out of its burnt gas (`burnt_gas_reward`). -/
  reward : Nat := 0
  logs : List String := []
  result : Option ExecutionStatus := none
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

/-- A refund receipt from the system account. -/
def refundReceipt (st : ChainState) (receiver : AccountId) (amount : Nat) : Receipt × ChainState :=
  let (id, st) := st.freshId
  ({ predecessorId := systemAccount, receiverId := receiver, receiptId := id,
     receipt := .action { signerId := systemAccount, signerPublicKey := [], gasPrice := 0,
                          actions := [.transfer amount] } }, st)

/-! ## Account id rules -/

/-- Can `predecessor` create `id`? Top-level names need the minimum length
(or the registrar), sub-accounts need their parent as predecessor. -/
def canCreateAccount (cfg : RuntimeConfig) (predecessor id : AccountId) : Bool :=
  if isImplicitAccount id then false
  else match id.splitOn "." with
    | [_] => id.length ≥ cfg.accountCreation.minAllowedTopLevelAccountLength
             || predecessor == cfg.accountCreation.registrarAccountId
    | parts => ".".intercalate (parts.drop 1) == predecessor

/-! ## Actions -/

def bytesOfString (s : String) : Bytes := s.toUTF8.toList
def stringOfBytes (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD ""

/-- Promise actions created by a contract become receipt actions. A missing
external decoder is a model issue, never a deployable placeholder module. -/
def actionOfPromise (codeOf : Bytes → ContractCode) : PromiseAction → Except RuntimeError Action
  | .createAccount => .ok .createAccount
  | .deployContract bytes => do
    let code := codeOf bytes
    if let some issue := code.decodeIssue then throw (.executionIssue issue)
    return .deployContract code
  | .functionCall m args amount gas => .ok (.functionCall (stringOfBytes m) args gas.toNat amount)
  | .transfer amount => .ok (.transfer amount)
  | .stake amount pk => .ok (.stake amount pk)
  | .addKey pk nonce perm =>
    let permission : AccessKeyPermission := match perm with
      | .fullAccess => .fullAccess
      | .functionCall allowance receiver methods =>
        .functionCall allowance (stringOfBytes receiver)
          (if methods.isEmpty then [] else (stringOfBytes methods).splitOn ",")
    .ok (.addKey pk { nonce := nonce.toNat, permission })
  | .deleteKey pk => .ok (.deleteKey pk)
  | .deleteAccount beneficiary => .ok (.deleteAccount (stringOfBytes beneficiary))

/-- Context of a receipt being applied. -/
structure ReceiptCtx where
  cfg : RuntimeConfig
  ap : ApplyState
  receipt : Receipt
  action : ActionReceipt
  promiseResults : List PromiseResult
  /-- Decoder for code deployed by contracts (not available in Lean yet). -/
  codeOf : Bytes → ContractCode

/-- Execute a function call and turn its promises into receipts. -/
def applyFunctionCall (c : ReceiptCtx) (method : String) (args : Bytes) (gas deposit : Nat)
    (isLast : Bool) : ExecM Unit := do
  let id := c.receipt.receiverId
  let account ← getAccount id
  let some code := account.code
    | throw (.functionCallError (.compilationError "CodeDoesNotExist"))
  if let some issue := code.decodeIssue then throw (.executionIssue issue)
  let st ← getState
  let ctx : VMContext := {
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
    randomSeed := c.ap.randomSeed
    outputDataReceivers := if isLast then c.action.outputDataReceivers.map fun d => bytesOfString d.receiverId else [] }
  let outcome := run c.cfg code.module code.size method ctx (st.contractStorage id)
  modify fun e => { e with logs := e.logs ++ outcome.logs
                           gasBurntForFunctionCall := e.gasBurntForFunctionCall + outcome.burntGas }
  burnGas outcome.burntGas
  useGas (outcome.usedGas - outcome.burntGas)
  match outcome.aborted with
  | some err => throw (.functionCallError err)
  | none =>
    putAccount id { account with amount := outcome.balance, storageUsage := outcome.storageUsage }
    modifyState (·.setContractStorage id outcome.storage)
    -- receipts created by the call
    let mut ids : Array ReceiptId := #[]
    for _ in outcome.receipts do
      ids := ids.push (← fresh)
    let mut outputs : Array (List DataReceiver) := Array.replicate outcome.receipts.length []
    let mut inputs : Array (List DataId) := Array.replicate outcome.receipts.length []
    for h : i in [0:outcome.receipts.length] do
      let spec := outcome.receipts[i]
      for dep in spec.dependencies do
        let dataId ← fresh
        outputs := outputs.modify dep (· ++ [{ dataId, receiverId := stringOfBytes spec.receiverId }])
        inputs := inputs.modify i (· ++ [dataId])
    -- the return value
    let outputReceivers := if isLast then c.action.outputDataReceivers else []
    match outcome.returnData with
    | .receiptIndex k =>
      outputs := outputs.modify k (· ++ outputReceivers)
      modify fun e => { e with result := some (.successReceiptId (ids[k]?.getD 0)) }
    | .value v =>
      for d in outputReceivers do
        let rid ← fresh
        emit { predecessorId := id, receiverId := d.receiverId, receiptId := rid,
               receipt := .data { dataId := d.dataId, data := some v } }
      modify fun e => { e with result := some (.successValue v) }
    | .none =>
      for d in outputReceivers do
        let rid ← fresh
        emit { predecessorId := id, receiverId := d.receiverId, receiptId := rid,
               receipt := .data { dataId := d.dataId, data := some [] } }
      modify fun e => { e with result := some (.successValue []) }
    for h : i in [0:outcome.receipts.length] do
      let spec := outcome.receipts[i]
      let actions ← match spec.actions.mapM (actionOfPromise c.codeOf) with
        | .ok actions => pure actions
        | .error error => throw error
      emit { predecessorId := id, receiverId := stringOfBytes spec.receiverId, receiptId := ids[i]?.getD 0,
             receipt := .action { signerId := c.action.signerId, signerPublicKey := c.action.signerPublicKey,
                                  gasPrice := c.action.gasPrice,
                                  outputDataReceivers := outputs[i]?.getD []
                                  inputDataIds := inputs[i]?.getD []
                                  actions := actions } }

def applyAction (c : ReceiptCtx) (isLast : Bool) : Action → ExecM Unit
  | .createAccount => do
    let id := c.receipt.receiverId
    if (← getState).account? id |>.isSome then throw (.accountAlreadyExists id)
    unless canCreateAccount c.cfg c.receipt.predecessorId id do
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
    | some a => putAccount id { a with amount := a.amount + deposit }
    | none =>
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
    if (st.accessKey? id pk).isSome then throw (.addKeyAlreadyExists id)
    let a ← getAccount id
    putAccount id { a with storageUsage := a.storageUsage + accessKeyStorageBytes pk key
      + c.cfg.fees.numExtraBytesRecord }
    modifyState (·.setAccessKey id pk key)
  | .deleteKey pk => do
    let id := c.receipt.receiverId
    let st ← getState
    let some key := st.accessKey? id pk | throw (.deleteKeyDoesNotExist id)
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
    set { (← get) with state := st.removeAccount id }
    modify fun e => { e with actorId := c.receipt.predecessorId }
    emit r

/-- `check_storage_stake`: the account must hold enough to pay for its state. -/
def checkStorageStake (cfg : RuntimeConfig) (id : AccountId) : ExecM Unit := do
  match (← getState).account? id with
  | some a =>
    let required := a.storageUsage * cfg.storageAmountPerByte
    if a.amount + a.locked < required then throw (.lackBalanceForState id (required - a.amount - a.locked))
  | none => pure ()

/-! ## Receipts -/

/-- The receiver must exist unless the receipt starts by creating it, or is a
transfer to an implicit account. -/
def checkReceiver (st : ChainState) (r : Receipt) (a : ActionReceipt) : Except RuntimeError Unit :=
  if (st.account? r.receiverId).isSome then .ok ()
  else match a.actions with
    | .createAccount :: _ => .ok ()
    | [.transfer _] => if isImplicitAccount r.receiverId then .ok () else .error (.accountDoesNotExist r.receiverId)
    | _ => .error (.accountDoesNotExist r.receiverId)

/-- Account existence is checked before permission for each individual action.
Implicit account creation requires a sole transfer from a non-system sender.
Reference: `actions.rs::check_account_existence` at `runtime/reference.json`. -/
def checkActionAccount (st : ChainState) (r : Receipt) (onlyAction : Bool)
    (action : Action) : Except RuntimeError Unit :=
  let accountExists := (st.account? r.receiverId).isSome
  match action with
  | .createAccount =>
    if accountExists then .error (.accountAlreadyExists r.receiverId)
    else if isImplicitAccount r.receiverId then .error (.onlyImplicitAccountCreationAllowed r.receiverId)
    else .ok ()
  | .transfer _ =>
    if accountExists || (onlyAction && !r.isRefund && isImplicitAccount r.receiverId) then .ok ()
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

/-- Apply the actions of an action receipt. Rolls back to the state at the
start on failure, then issues refunds either way. -/
def applyActionReceipt (c : ReceiptCtx) (st0 : ChainState) : Exec :=
  let f := c.cfg.fees.actionFees
  let receiver := c.receipt.receiverId
  -- gas prepaid for this receipt: its creation and action execution fees, the execution fee
  -- and the gas attached to its function calls. Dependency data execution fees
  -- were already burnt by the producer when scheduling this callback.
  let receiptGas := f.newActionReceipt.execution + Fees.totalExec f receiver c.action.actions
    + Fees.totalPrepaid c.action.actions
  -- refunds (sent by the system account) burn no gas
  let isRefund := c.receipt.isRefund
  let body : ExecM Unit := do
    unless isRefund do
      burnGas f.newActionReceipt.execution
    let n := c.action.actions.length
    for h : i in [0:n] do
      let act := c.action.actions[i]
      unless isRefund do burnGas (Fees.exec f receiver act)
      match checkActionAccount (← getState) c.receipt (n == 1) act with
      | .error e => throw e
      | .ok () => pure ()
      match checkActorPermissions (← get).actorId receiver act with
      | .error e => throw e
      | .ok () => pure ()
      applyAction c (i + 1 == n) act
    checkStorageStake c.cfg receiver
  let exec0 : Exec := { state := st0, actorId := c.receipt.predecessorId }
  let (exec, failed) := match (body.run.run exec0) with
    | (.ok (), e) => (e, none)
    | (.error err, e) => (e, some err)
  -- roll back on failure: keep gas, drop receipts and state changes
  let exec := match failed with
    | some err => { exec with state := st0, newReceipts := [], gasUsed := exec.gasBurnt,
                              result := some (.failure err) }
    | none => exec
  let _ := failed
  -- refunds: unspent gas to the signer, the deposits to the predecessor on failure
  let gasRefund := receiptGas - exec.gasUsed
  let tokensRefund := gasRefund * c.action.gasPrice
  let depositRefund := if failed.isSome then Fees.totalDeposit c.action.actions else 0
  let exec := if depositRefund > 0 && c.receipt.predecessorId != systemAccount then
      let (r, st) := refundReceipt exec.state c.receipt.predecessorId depositRefund
      { exec with state := st, newReceipts := exec.newReceipts ++ [r] }
    else exec
  let exec := if tokensRefund > 0 && c.action.signerId != systemAccount then
      let (r, st) := refundReceipt exec.state c.action.signerId tokensRefund
      { exec with state := st, newReceipts := exec.newReceipts ++ [r] }
    else exec
  -- The surviving receiver earns the burnt function-call reward even when
  -- execution failed and its state changes were rolled back (nearcore lib.rs).
  let exec :=
      let (num, den) := c.cfg.fees.burntGasReward
      let reward := exec.gasBurntForFunctionCall * num / den * c.action.gasPrice
      match exec.state.account? receiver with
      | some a => { exec with state := exec.state.setAccount receiver { a with amount := a.amount + reward }
                              reward := reward }
      | none => exec
  -- data receipts for failed executions: receivers learn the failure
  let exec := if failed.isSome then
      let (st, rs) := c.action.outputDataReceivers.foldl
        (fun (acc : ChainState × List Receipt) (d : DataReceiver) =>
          let (st, rs) := acc
          let (id, st) := st.freshId
          (st, rs ++ [({ predecessorId := receiver, receiverId := d.receiverId, receiptId := id,
                         receipt := .data { dataId := d.dataId, data := none } } : Receipt)]))
        (exec.state, [])
      { exec with state := st, newReceipts := exec.newReceipts ++ rs }
    else exec
  { exec with result := some (exec.result.getD (.successValue [])) }

/-- Outcome of an executed receipt. -/
def outcomeOf (r : Receipt) (gasPrice : Nat) (e : Exec) : ExecutionOutcome :=
  { executorId := r.receiverId
    status := e.result.getD (.successValue [])
    logs := e.logs
    receiptIds := e.newReceipts.map (·.receiptId)
    gasBurnt := e.gasBurnt
    tokensBurnt := e.gasBurnt * gasPrice }

/-- Result of processing one receipt: state, new receipts, outcomes, and the
yocto paid to contracts as gas reward (which are not burnt). -/
structure Processed where
  state : ChainState
  receipts : List Receipt := []
  outcomes : List (ReceiptId × ExecutionOutcome) := []
  rewards : Nat := 0
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
        { state := e.state, receipts := e.newReceipts, outcomes := [(r.receiptId, outcomeOf r a.gasPrice e)],
          rewards := e.reward }
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

/-- `verify_and_charge_transaction`: signer, key, nonce, permission and
balance checks; charges the cost; bumps the nonce; returns the receipt. -/
def convertTransaction (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (tx : Transaction) :
    Except RuntimeError (ChainState × Receipt × Fees.TxCost) := do
  let some signer := st.account? tx.signerId | throw (.invalidSigner tx.signerId)
  let some key := st.accessKey? tx.signerId tx.publicKey | throw (.invalidAccessKey "AccessKeyNotFound")
  if tx.nonce ≤ key.nonce then throw (.invalidNonce tx.nonce key.nonce)
  if tx.actions.length > cfg.wasm.limits.maxActionsPerReceipt then
    throw (.tooManyActions tx.actions.length cfg.wasm.limits.maxActionsPerReceipt)
  let cost := Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions
  let key' ← match key.permission with
    | .fullAccess => pure { key with nonce := tx.nonce }
    | .functionCall allowance receiver methods =>
      match tx.actions with
      | [.functionCall m _ _ deposit] =>
        if tx.receiverId != receiver then throw (.invalidAccessKey "ReceiverMismatch")
        if deposit > 0 then throw (.invalidAccessKey "DepositWithFunctionCall")
        if !(methods.isEmpty || methods.contains m) then throw (.invalidAccessKey "MethodNameMismatch")
        match allowance with
        | some al =>
          if al < cost.total then throw (.invalidAccessKey "NotEnoughAllowance")
          pure { nonce := tx.nonce, permission := .functionCall (some (al - cost.total)) receiver methods }
        | none => pure { key with nonce := tx.nonce }
      | _ => throw (.invalidAccessKey "RequiresFullAccess")
  if signer.amount < cost.total then throw (.notEnoughBalance tx.signerId signer.amount cost.total)
  let signer' := { signer with amount := signer.amount - cost.total }
  if signer'.amount + signer'.locked < signer'.storageUsage * cfg.storageAmountPerByte then
    throw (.lackBalanceForState tx.signerId (signer'.storageUsage * cfg.storageAmountPerByte - signer'.amount))
  let st := (st.setAccount tx.signerId signer').setAccessKey tx.signerId tx.publicKey key'
  let (id, st) := st.freshId
  let action : ActionReceipt :=
    { signerId := tx.signerId
      signerPublicKey := tx.publicKey
      gasPrice := ap.gasPrice
      actions := tx.actions }
  let receipt : Receipt :=
    { predecessorId := tx.signerId
      receiverId := tx.receiverId
      receiptId := id
      receipt := .action action }
  return (st, receipt, cost)

/-- `Runtime::apply`. Transactions first; only signer-is-receiver receipts
are local. Other transaction receipts are outgoing work for a later chunk.
Local, delayed and incoming receipts execute in that order; receipts beyond
the gas limit are delayed to the next apply. -/
private def applyAttempt (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) : ApplyResult := Id.run do
  let initial := st
  let mut st := st
  let mut outcomes : List (ReceiptId × ExecutionOutcome) := []
  let mut outgoing : List Receipt := []
  let mut localReceipts : List Receipt := []
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
      outcomes := outcomes ++ [(0, { executorId := tx.signerId, status := .failure e })]
  let queue := localReceipts ++ st.delayed ++ incoming
  st := { st with delayed := [] }
  let mut gasUsed := 0
  let mut overLimit := false
  for r in queue do
    if overLimit then
      st := { st with delayed := st.delayed ++ [r] }
    else
      let p := processReceipt cfg ap codeOf st r
      if let some issue := p.issue then
        return { state := initial, outgoing := [], outcomes := [], tokensBurnt := 0, issue := some issue }
      st := p.state
      outgoing := outgoing ++ p.receipts
      outcomes := outcomes ++ p.outcomes
      for (_, o) in p.outcomes do
        gasUsed := gasUsed + o.gasBurnt
        tokensBurnt := tokensBurnt + o.tokensBurnt
      tokensBurnt := tokensBurnt - p.rewards
      if let some limit := ap.gasLimit then
        if gasUsed ≥ limit then overLimit := true
  return { state := st, outgoing, outcomes, tokensBurnt }

/-- Commit a supported chunk. Model limitations invalidate the entire attempt:
no fees, refunds, nonces, receipt consumption, or state changes are committed. -/
def apply (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) : ApplyResult :=
  let result := applyAttempt cfg ap codeOf st txs incoming
  if result.issue.isSome then
    { result with state := st, outgoing := [], outcomes := [], tokensBurnt := 0 }
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

end Near
