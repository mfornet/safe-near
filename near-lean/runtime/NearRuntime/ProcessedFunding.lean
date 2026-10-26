import NearRuntime.ReceiptQueueFrame

namespace Near
open Wasm Wasm.Near

/-- Account funds, queued receipt backing and newly emitted receipt backing. -/
def Processed.totalFunds (cfg : RuntimeConfig) (processed : Processed) : Nat :=
  processed.state.totalFunds cfg + receiptsFunds cfg processed.receipts

def Processed.netTokensBurnt (processed : Processed) : Nat :=
  (processed.outcomes.map (fun outcome => outcome.2.tokensBurnt)).sum + processed.otherTokensBurnt - processed.rewards

/-- Input data is consumed as routing metadata; it carries no token asset. -/
def consumeReceiptDataState (st : ChainState) (action : ActionReceipt) : ChainState :=
  { st with receivedData := st.receivedData.filter fun entry => !action.inputDataIds.contains entry.1 }

/-- Promise results are read before consumption, exactly as in the executable
ready-action branch. The decoder remains the runtime's explicit code boundary. -/
def readyActionContext (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) : ReceiptCtx :=
  { cfg := cfg
    ap := ap
    receipt := receipt
    action := action
    codeOf := decoder
    vmYields := yieldsOf st receipt.receiverId
    promiseResults := action.inputDataIds.map fun id =>
      match Assoc.lookup st.receivedData id with
      | some (some bytes) => .successful bytes
      | _ => .failed }

def Exec.routingIssue (exec : Exec) : Option ExecutionIssue :=
  match exec.result with
  | some (.failure error) => error.issue?
  | _ => none

def processedExecOutput (receipt : Receipt) (exec : Exec) : Processed :=
  { storageAccounting := exec.storageAccounting
    state := exec.state
    receipts := exec.newReceipts
    identityBirths := [{ parent := receipt.receiptId, children := exec.newReceipts.map (·.receiptId), vmActions := exec.vmIdentityBirths }]
    outcomes := [(receipt.receiptId, outcomeOf receipt exec)]
    rewards := exec.reward
    otherTokensBurnt := exec.otherTokensBurnt
    subsidizedAmount := exec.subsidizedAmount
    execs := [(receipt, exec)] }

def processedOfExec (fallback : ChainState) (receipt : Receipt) (exec : Exec) : Processed :=
  match exec.routingIssue with
  | some issue => { state := fallback, issue := some (receipt.receiptId, issue) }
  | none => processedExecOutput receipt exec

/-- Unsupported/incomplete execution cannot be treated as a committed funded
receipt merely by inspecting its speculative execution ledger. -/
theorem processedOfExec_supported (fallback : ChainState) (receipt : Receipt) (exec : Exec)
    (hsupported : (processedOfExec fallback receipt exec).issue = none) :
    processedOfExec fallback receipt exec = processedExecOutput receipt exec := by
  cases he : exec.routingIssue with
  | none => simp only [processedOfExec, he]
  | some issue => simp [processedOfExec, he] at hsupported

/-- Running an action receipt is the real execution followed by the routing of its outcome. -/
theorem runActionReceipt_eq (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (results : List PromiseResult) :
    runActionReceipt cfg ap decoder st receipt action results =
      processedOfExec st receipt (applyActionReceipt
        { cfg, ap, receipt, action, promiseResults := results, codeOf := decoder
          vmYields := yieldsOf st receipt.receiverId } st) := by
  rfl

/-- Running a stored receipt leaves the routing-owned queues alone (or falls back to its input). -/
theorem runActionReceipt_receiptQueues (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (results : List PromiseResult) :
    (runActionReceipt cfg ap decoder st receipt action results).state.receiptQueues = st.receiptQueues := by
  rw [runActionReceipt_eq]
  unfold processedOfExec
  split
  · rfl
  · exact applyActionReceipt_receiptQueues _ st

/-- A usable unfolding rule for the actual ready-action processing path. -/
theorem processReceipt_ready (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = none)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true) :
    processReceipt cfg ap decoder st receipt =
      processedOfExec (consumeReceiptDataState st action) receipt
        (applyActionReceipt (readyActionContext cfg ap decoder st receipt action) (consumeReceiptDataState st action)) := by
  rw [processReceipt]
  simp only [haction, hyield, hready, ite_true]
  rfl

/-- Running a receipt whose inputs are in hand conserves the complete runtime-state ledger,
including untouched postponed/delayed/yielded assets, new receipts, net burn and subsidy.
Both ordinary actions and constructor-shaped system refunds are covered. -/
theorem runActionReceipt_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (results : List PromiseResult)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (runActionReceipt cfg ap decoder st receipt action results).issue = none) :
    let processed := runActionReceipt cfg ap decoder st receipt action results
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  let ctx : ReceiptCtx :=
    { cfg, ap, receipt, action, promiseResults := results, codeOf := decoder
      vmYields := yieldsOf st receipt.receiverId }
  let exec := applyActionReceipt ctx st
  have hshape' : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, haction] using hshape
  have hf := applyActionReceipt_financial_conservation ctx st hwf haction hshape' hnew hratio
  change exec.totalFunds cfg + exec.netTokensBurnt = st.totalBalance + Fees.receiptFunds cfg receipt + exec.subsidizedAmount at hf
  have hqueues := applyActionReceipt_queuedFunds ctx st
  change exec.state.queuedFunds cfg = st.queuedFunds cfg at hqueues
  have hp := runActionReceipt_eq cfg ap decoder st receipt action results
  change runActionReceipt cfg ap decoder st receipt action results = processedOfExec st receipt exec at hp
  have hout : processedOfExec st receipt exec = processedExecOutput receipt exec :=
    processedOfExec_supported st receipt exec (by rw [← hp]; exact hsupported)
  dsimp only
  rw [hp, hout]
  change exec.state.totalBalance + exec.state.queuedFunds cfg + receiptsFunds cfg exec.newReceipts + exec.netTokensBurnt =
    st.totalBalance + st.queuedFunds cfg + Fees.receiptFunds cfg receipt + exec.subsidizedAmount
  rw [hqueues]
  unfold Exec.totalFunds at hf
  omega

theorem runActionReceipt_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (results : List PromiseResult)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt)
    (hsupported : (runActionReceipt cfg ap decoder st receipt action results).issue = none) :
    (runActionReceipt cfg ap decoder st receipt action results).state.AccountsUnique := by
  let ctx : ReceiptCtx :=
    { cfg, ap, receipt, action, promiseResults := results, codeOf := decoder
      vmYields := yieldsOf st receipt.receiverId }
  let exec := applyActionReceipt ctx st
  have hshape' : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, haction] using hshape
  have hu := applyActionReceipt_financial_accountsUnique ctx st hwf hshape'
  have hp := runActionReceipt_eq cfg ap decoder st receipt action results
  change runActionReceipt cfg ap decoder st receipt action results = processedOfExec st receipt exec at hp
  have hout := processedOfExec_supported st receipt exec (by rw [← hp]; exact hsupported)
  rw [hp, hout]
  exact hu

/-- Ready receipt processing conserves the complete runtime-state ledger. -/
theorem processReceipt_ready_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = none)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  let before := consumeReceiptDataState st action
  let ctx := readyActionContext cfg ap decoder st receipt action
  let exec := applyActionReceipt ctx before
  have hshape' : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, haction] using hshape
  have hf := applyActionReceipt_financial_conservation ctx before hwf haction hshape' hnew hratio
  change exec.totalFunds cfg + exec.netTokensBurnt = st.totalBalance + Fees.receiptFunds cfg receipt + exec.subsidizedAmount at hf
  have hqueues := applyActionReceipt_queuedFunds ctx before
  change exec.state.queuedFunds cfg = st.queuedFunds cfg at hqueues
  have hp := processReceipt_ready cfg ap decoder st receipt action haction hyield hready
  change processReceipt cfg ap decoder st receipt = processedOfExec before receipt exec at hp
  have hout : processedOfExec before receipt exec = processedExecOutput receipt exec :=
    processedOfExec_supported before receipt exec (by rw [← hp]; exact hsupported)
  dsimp only
  rw [hp, hout]
  change exec.state.totalBalance + exec.state.queuedFunds cfg + receiptsFunds cfg exec.newReceipts + exec.netTokensBurnt =
    st.totalBalance + st.queuedFunds cfg + Fees.receiptFunds cfg receipt + exec.subsidizedAmount
  rw [hqueues]
  unfold Exec.totalFunds at hf
  omega

/-- Ready processing also retains the account uniqueness premise for the next
receipt. Queue/domain/id consistency remains a separate routing invariant. -/
theorem processReceipt_ready_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = none)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true)
    (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  let before := consumeReceiptDataState st action
  let ctx := readyActionContext cfg ap decoder st receipt action
  let exec := applyActionReceipt ctx before
  have hshape' : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, haction] using hshape
  have hu := applyActionReceipt_financial_accountsUnique ctx before hwf hshape'
  have hp := processReceipt_ready cfg ap decoder st receipt action haction hyield hready
  change processReceipt cfg ap decoder st receipt = processedOfExec before receipt exec at hp
  have hout := processedOfExec_supported before receipt exec (by rw [← hp]; exact hsupported)
  rw [hp, hout]
  exact hu

/-- Waiting receipts retain their complete backing inside the postponed map;
no output receipt or burn observation is needed until execution becomes ready. -/
theorem processReceipt_waiting_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = none)
    (hmissing : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = false)
    (hunique : Assoc.KeysUnique st.postponed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  dsimp only
  rw [processReceipt_waiting cfg ap decoder st receipt action haction hyield hmissing]
  simpa only [Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
    Nat.add_zero, Nat.sub_zero] using postponeActionState_funds cfg st receipt action hunique hfresh

/-- A yielded receipt is stored with its complete backing; processing it burns and emits nothing. -/
theorem processReceipt_yield_unfold (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (dataId : Bytes)
    (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = some dataId) :
    processReceipt cfg ap decoder st receipt =
      if (Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId)).isSome then
        { state := st, storageAccounting := ap.storageAccounting
          issue := some (receipt.receiptId, .unsupportedAction "duplicate yielded data id") }
      else
        { state := { st with yieldReceipts := Assoc.insert st.yieldReceipts (receipt.receiverId, dataId) receipt },
          storageAccounting := ap.storageAccounting } := by
  rw [processReceipt]
  simp only [haction, hyield]

theorem processReceipt_yield_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt) (dataId : Bytes)
    (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = some dataId)
    (hyunique : Assoc.KeysUnique st.yieldReceipts)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  have hu := processReceipt_yield_unfold cfg ap decoder st receipt action dataId haction hyield
  dsimp only
  rw [hu] at hsupported ⊢
  by_cases hs : (Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId)).isSome = true
  · simp [hs] at hsupported
  · have hfresh : Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) = none := by
      cases h : Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) with
      | none => rfl
      | some _ => simp [h] at hs
    simp only [hs, Bool.false_eq_true, ite_false, Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds,
      List.map_nil, List.sum_nil, Nat.add_zero, Nat.sub_zero]
    exact yieldInsert_funds cfg st _ receipt hyunique hfresh

/-- Both actual action-receipt routing branches share one complete funding law.
The postponed identifier premise prevents overwriting a previously owned asset. -/
theorem processReceipt_action_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hunique : Assoc.KeysUnique st.postponed) (hyunique : Assoc.KeysUnique st.yieldReceipts)
    (hfresh : Assoc.lookup st.postponed receipt.receiptId = none)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  cases hy : action.yieldDataId with
  | some dataId => exact processReceipt_yield_conservation cfg ap decoder st receipt action dataId haction hy hyunique hsupported
  | none =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | true => exact processReceipt_ready_conservation cfg ap decoder st receipt action hwf haction hy he hshape hnew hratio hsupported
    | false => exact processReceipt_waiting_conservation cfg ap decoder st receipt action haction hy he hunique hfresh

theorem processReceipt_action_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  cases hy : action.yieldDataId with
  | some dataId =>
    have hu := processReceipt_yield_unfold cfg ap decoder st receipt action dataId haction hy
    rw [hu] at hsupported ⊢
    by_cases hs : (Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId)).isSome = true
    · simp [hs] at hsupported
    · simp only [hs, Bool.false_eq_true, ite_false]
      exact hwf
  | none =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | true => exact processReceipt_ready_accountsUnique cfg ap decoder st receipt action hwf haction hy he hshape hsupported
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action haction hy he]
      exact hwf

/-! ### Instant receipts -/

/-- The receipt step of `processInstants`, for properties that follow a receipt through it. -/
def instantStep (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (acc : Processed) (r : Receipt) : Processed :=
  processReceipt cfg { ap with storageAccounting := acc.storageAccounting } codeOf acc.state r

/-- The accumulator after an instant receipt ran: its outgoing receipts that are not instant are
sent out, the instant ones queue behind the pending instants. -/
def instantAccumulate (acc p : Processed) : Processed :=
  acc.append { p with receipts := p.receipts.filter fun x => !x.isInstant }

/-- Induction over the instant receipts a receipt created. `Inv` holds along the work list, `Fin`
is what the finished (or abandoned) run satisfies; an unsupported instant abandons the run. -/
theorem processInstants_induction (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (Inv : Processed → List Receipt → Prop) (Fin : Processed → Prop)
    (hfin : ∀ acc, Inv acc [] → Fin acc)
    (hissue : ∀ acc pending issue, issue.isSome = true → Inv acc pending → Fin { acc with issue := issue })
    (hstep : ∀ acc r rest, Inv acc (r :: rest) → r.fundedShape = true →
      (instantStep cfg ap codeOf acc r).issue = none →
      Inv (instantAccumulate acc (instantStep cfg ap codeOf acc r))
        (rest ++ (instantStep cfg ap codeOf acc r).receipts.filter Receipt.isInstant)) :
    ∀ fuel acc pending, Inv acc pending → Fin (processInstants cfg ap codeOf fuel acc pending) := by
  intro fuel
  induction fuel with
  | zero =>
    intro acc pending h
    cases pending with
    | nil => exact hfin acc h
    | cons r rest => exact hissue acc _ _ rfl h
  | succ fuel ih =>
    intro acc pending h
    cases pending with
    | nil => exact hfin acc h
    | cons r rest =>
      unfold processInstants
      by_cases hs : r.fundedShape = true
      · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hi : (instantStep cfg ap codeOf acc r).issue.isSome = true
        · simp only [instantStep] at hi
          simp only [hi, ↓reduceIte]
          exact hissue acc _ _ hi h
        · have hnone : (instantStep cfg ap codeOf acc r).issue = none := by simpa using hi
          simp only [instantStep] at hnone hi
          simp only [hi, Bool.false_eq_true, ↓reduceIte]
          exact ih _ _ (hstep acc r rest h hs hnone)
      · have hs' : (!r.fundedShape) = true := by simpa using hs
        simp only [hs', ↓reduceIte]
        exact hissue acc _ _ rfl h

/-- Induction over a receipt and the instant receipts it creates. -/
theorem processWithInstants_induction (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (Inv : Processed → List Receipt → Prop) (Fin : Processed → Prop) (Start : ChainState → Receipt → Prop)
    (hfin : ∀ acc, Inv acc [] → Fin acc)
    (hissue : ∀ acc pending issue, issue.isSome = true → Inv acc pending → Fin { acc with issue := issue })
    (hstep : ∀ acc r rest, Inv acc (r :: rest) → r.fundedShape = true →
      (instantStep cfg ap codeOf acc r).issue = none →
      Inv (instantAccumulate acc (instantStep cfg ap codeOf acc r))
        (rest ++ (instantStep cfg ap codeOf acc r).receipts.filter Receipt.isInstant))
    (hfirstIssue : ∀ st r, Start st r → (processReceipt cfg ap codeOf st r).issue ≠ none →
      Fin (processReceipt cfg ap codeOf st r))
    (hfirst : ∀ st r, Start st r → (processReceipt cfg ap codeOf st r).issue = none →
      Inv { processReceipt cfg ap codeOf st r with
              receipts := (processReceipt cfg ap codeOf st r).receipts.filter fun x => !x.isInstant }
        ((processReceipt cfg ap codeOf st r).receipts.filter Receipt.isInstant)) :
    ∀ st r, Start st r → Fin (processWithInstants cfg ap codeOf st r) := by
  intro st r hstart
  unfold processWithInstants
  by_cases hi : (processReceipt cfg ap codeOf st r).issue.isSome = true
  · simp only [hi, ↓reduceIte]
    exact hfirstIssue st r hstart (by intro hn; simp [hn] at hi)
  · have hnone : (processReceipt cfg ap codeOf st r).issue = none := by simpa using hi
    simp only [hi, Bool.false_eq_true, ↓reduceIte]
    exact processInstants_induction cfg ap codeOf Inv Fin hfin hissue hstep _ _ _
      (hfirst st r hstart hnone)

end Near
