import NearRuntime.FreshReceiptIds

namespace Near
open Wasm.Near

theorem failureDataFold_freshIds (receiver : AccountId) (outputs : List DataReceiver) (initial : ChainState) :
    let result := outputs.foldl (failureDataStep receiver) (initial, [])
    initial.nextId ≤ result.1.nextId ∧ ReceiptList.FreshIds initial.nextId result.1.nextId result.2 := by
  apply foldl_preserves (fun pair : ChainState × List Receipt => initial.nextId ≤ pair.1.nextId ∧
    ReceiptList.FreshIds initial.nextId pair.1.nextId pair.2)
  · intro pair output hp
    refine ⟨hp.1.trans (Nat.le_succ _), ?_⟩
    apply ReceiptList.FreshIds.append hp.2 _ hp.1 (Nat.le_succ _)
    constructor
    · simp
    · intro receipt hm
      have he := List.mem_singleton.mp hm
      subst receipt
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  · exact ⟨Nat.le_refl _, ReceiptList.FreshIds.empty _ _⟩

theorem Exec.addFailureData_freshIds (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) (lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.addFailureData receiver outputs).FreshReceiptIds lower := by
  have hf := failureDataFold_freshIds receiver outputs exec.state
  exact ReceiptList.FreshIds.append h hf.2 hfloor hf.1

theorem completionDataFold_freshIds (receiver : AccountId) (data : Option Bytes) (outputs : List DataReceiver) (initial : ChainState) :
    let result := outputs.foldl (completionDataStep receiver data) (initial, [])
    initial.nextId ≤ result.1.nextId ∧ ReceiptList.FreshIds initial.nextId result.1.nextId result.2 := by
  apply foldl_preserves (fun pair : ChainState × List Receipt => initial.nextId ≤ pair.1.nextId ∧
    ReceiptList.FreshIds initial.nextId pair.1.nextId pair.2)
  · intro pair output hp
    refine ⟨hp.1.trans (Nat.le_succ _), ?_⟩
    apply ReceiptList.FreshIds.append hp.2 _ hp.1 (Nat.le_succ _)
    constructor
    · simp
    · intro receipt hm
      have he := List.mem_singleton.mp hm
      subst receipt
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  · exact ⟨Nat.le_refl _, ReceiptList.FreshIds.empty _ _⟩

theorem Exec.addCompletionData_freshIds (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) (lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.addCompletionData receiver outputs).FreshReceiptIds lower := by
  unfold Exec.addCompletionData
  dsimp only
  split
  · exact h
  · rename_i data he
    have hf := completionDataFold_freshIds receiver data outputs exec.state
    exact ReceiptList.FreshIds.append h hf.2 hfloor hf.1

theorem Exec.creditReceiptReward_freshIds (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice lower : Nat) (h : exec.FreshReceiptIds lower) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).FreshReceiptIds lower := by
  unfold Exec.creditReceiptReward
  split <;> exact h

/-- Failure discards speculative receipts and allocations before constructing
the final list; success retains the collision-free speculative output interval. -/
theorem finalizeReceipt_freshIds (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hraw : raw.FreshReceiptIds st.nextId) (hmono : st.nextId ≤ raw.state.nextId) :
    (finalizeReceipt c st raw failed).FreshReceiptIds st.nextId := by
  let base := rollbackReceipt st raw failed
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) base.gasUsed base.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (base.state.account? c.receipt.receiverId).isSome && failed.isNone)
  let charged := { base with
    tokensBurnt := if c.receipt.isRefund then 0 else settlement.tokensBurnt
    otherTokensBurnt := if c.receipt.isRefund && failed.isSome then Fees.totalDeposit c.action.actions else 0 }
  let depositRefund := if failed.isSome then Fees.totalDeposit c.action.actions else 0
  let gasRefund := if c.receipt.isRefund then 0 else settlement.refund
  let balance := if depositRefund > 0 && c.receipt.predecessorId != systemAccount then
    charged.addBalanceRefund c.receipt.predecessorId depositRefund else charged
  let gas := if gasRefund > 0 && c.action.signerId != systemAccount then
    balance.addGasRefund c.action.signerId c.action.signerPublicKey gasRefund else balance
  let rewarded := gas.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let finished := if failed.isSome then rewarded.addFailureData c.receipt.receiverId c.action.outputDataReceivers else rewarded.addCompletionData c.receipt.receiverId c.action.outputDataReceivers
  have hbase : base.FreshReceiptIds st.nextId := by
    cases failed with
    | none => exact hraw
    | some error => exact ReceiptList.FreshIds.empty _ _
  have hnbase : st.nextId ≤ base.state.nextId := by
    cases failed <;> first | exact hmono | exact Nat.le_refl _
  have hcharged : charged.FreshReceiptIds st.nextId := hbase
  have hbalance : balance.FreshReceiptIds st.nextId := by
    dsimp only [balance]
    split
    · exact Exec.addBalanceRefund_freshIds charged _ _ _ hcharged hnbase
    · exact hcharged
  have hnbalance : st.nextId ≤ balance.state.nextId := by
    dsimp only [balance]
    split
    · exact hnbase.trans (Exec.addBalanceRefund_nextId_mono charged _ _)
    · exact hnbase
  have hgas : gas.FreshReceiptIds st.nextId := by
    dsimp only [gas]
    split
    · exact Exec.addGasRefund_freshIds balance _ _ _ _ hbalance hnbalance
    · exact hbalance
  have hngas : st.nextId ≤ gas.state.nextId := by
    dsimp only [gas]
    split
    · exact hnbalance.trans (Exec.addGasRefund_nextId_mono balance _ _ _)
    · exact hnbalance
  have hrewarded : rewarded.FreshReceiptIds st.nextId :=
    Exec.creditReceiptReward_freshIds gas _ _ _ _ _ hgas
  have hnrewarded : st.nextId ≤ rewarded.state.nextId := by
    rw [Exec.creditReceiptReward_nextId]
    exact hngas
  have hfinished : finished.FreshReceiptIds st.nextId := by
    dsimp only [finished]
    split
    · exact Exec.addFailureData_freshIds rewarded _ _ _ hrewarded hnrewarded
    · exact Exec.addCompletionData_freshIds rewarded _ _ _ hrewarded hnrewarded
  exact hfinished

theorem applyActionReceipt_freshIds (c : ReceiptCtx) (st : ChainState) :
    (applyActionReceipt c st).FreshReceiptIds st.nextId :=
  finalizeReceipt_freshIds c st _ _ (runReceiptActions_freshIds c st) (runReceiptActions_nextId_mono c st)

/-- Public receipt outputs are collision-free and newly allocated, without any
validity, financial-scope, input-bound or successful-execution assumption. -/
theorem processReceipt_freshIds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) :
    ReceiptList.FreshIds st.nextId (processReceipt cfg ap decoder st receipt).state.nextId
      (processReceipt cfg ap decoder st receipt).receipts := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action hr he]
      exact ReceiptList.FreshIds.empty _ _
    | true =>
      rw [processReceipt_ready cfg ap decoder st receipt action hr he]
      unfold processedOfExec
      split
      · exact ReceiptList.FreshIds.empty _ _
      · exact applyActionReceipt_freshIds (readyActionContext cfg ap decoder st receipt action)
          (consumeReceiptDataState st action)
  | data data =>
    rw [processReceipt_data cfg ap decoder st receipt data hr]
    cases hroute : Assoc.lookup st.postponedByData data.dataId with
    | none => exact ReceiptList.FreshIds.empty _ _
    | some id =>
      simp only
      cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
      | false => simp only [Bool.false_eq_true, ite_false]; exact ReceiptList.FreshIds.empty _ _
      | true =>
        simp only [ite_true]
        cases hwaiting : Assoc.lookup st.postponed id with
        | none => exact ReceiptList.FreshIds.empty _ _
        | some waiting =>
          exact processReceipt_freshIds cfg ap decoder
            (releasePostponedState (receivePostponedDataState st data) id) waiting
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

end Near
