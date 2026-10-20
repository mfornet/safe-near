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
    promiseResults := action.inputDataIds.map fun id =>
      match Assoc.lookup st.receivedData id with
      | some (some bytes) => .successful bytes
      | _ => .failed }

def Exec.routingIssue (exec : Exec) : Option ExecutionIssue :=
  match exec.result with
  | some (.failure error) => error.issue?
  | _ => none

def processedExecOutput (receipt : Receipt) (exec : Exec) : Processed :=
  { state := exec.state
    receipts := exec.newReceipts
    outcomes := [(receipt.receiptId, outcomeOf receipt exec)]
    rewards := exec.reward
    otherTokensBurnt := exec.otherTokensBurnt
    subsidizedAmount := exec.subsidizedAmount }

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

/-- A usable unfolding rule for the actual ready-action processing path. -/
theorem processReceipt_ready (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true) :
    processReceipt cfg ap decoder st receipt =
      processedOfExec (consumeReceiptDataState st action) receipt
        (applyActionReceipt (readyActionContext cfg ap decoder st receipt action) (consumeReceiptDataState st action)) := by
  rw [processReceipt]
  simp only [haction, hready, ite_true]
  rfl

/-- Ready receipt processing conserves the complete runtime-state ledger,
including untouched postponed/delayed assets, new receipts, net burn and subsidy.
Both ordinary actions and constructor-shaped system refunds are covered. -/
theorem processReceipt_ready_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
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
  have hp := processReceipt_ready cfg ap decoder st receipt action haction hready
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
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true)
    (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  let before := consumeReceiptDataState st action
  let ctx := readyActionContext cfg ap decoder st receipt action
  let exec := applyActionReceipt ctx before
  have hshape' : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, haction] using hshape
  have hu := applyActionReceipt_financial_accountsUnique ctx before hwf hshape'
  have hp := processReceipt_ready cfg ap decoder st receipt action haction hready
  change processReceipt cfg ap decoder st receipt = processedOfExec before receipt exec at hp
  have hout := processedOfExec_supported before receipt exec (by rw [← hp]; exact hsupported)
  rw [hp, hout]
  exact hu

/-- Waiting receipts retain their complete backing inside the postponed map;
no output receipt or burn observation is needed until execution becomes ready. -/
theorem processReceipt_waiting_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action)
    (hmissing : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = false)
    (hunique : Assoc.KeysUnique st.postponed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  dsimp only
  rw [processReceipt_waiting cfg ap decoder st receipt action haction hmissing]
  simpa only [Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
    Nat.add_zero, Nat.sub_zero] using postponeActionState_funds cfg st receipt action hunique hfresh

/-- Both actual action-receipt routing branches share one complete funding law.
The postponed identifier premise prevents overwriting a previously owned asset. -/
theorem processReceipt_action_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hunique : Assoc.KeysUnique st.postponed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
  | true => exact processReceipt_ready_conservation cfg ap decoder st receipt action hwf haction he hshape hnew hratio hsupported
  | false => exact processReceipt_waiting_conservation cfg ap decoder st receipt action haction he hunique hfresh

theorem processReceipt_action_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
  | true => exact processReceipt_ready_accountsUnique cfg ap decoder st receipt action hwf haction he hshape hsupported
  | false =>
    rw [processReceipt_waiting cfg ap decoder st receipt action haction he]
    exact hwf

end Near
