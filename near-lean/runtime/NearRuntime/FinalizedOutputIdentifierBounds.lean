import NearRuntime.ActionOutputIdentifierBounds

namespace Near
open Wasm.Near

/-- The real failed-data fold bounds both freshly allocated envelopes and the
inherited dependency ids they carry. -/
theorem failureDataFold_outputIds (receiver : AccountId) (outputs : List DataReceiver) (initial : ChainState)
    (houtputs : ∀ output ∈ outputs, output.dataId < initial.nextId) :
    let result := outputs.foldl (failureDataStep receiver) (initial, [])
    initial.nextId ≤ result.1.nextId ∧
      ∀ receipt ∈ result.2, ∀ id ∈ receipt.liveIds, id < result.1.nextId := by
  apply foldl_preserves_mem (fun pair : ChainState × List Receipt => initial.nextId ≤ pair.1.nextId ∧
    ∀ receipt ∈ pair.2, ∀ id ∈ receipt.liveIds, id < pair.1.nextId)
  · intro pair output hm hp
    constructor
    · exact hp.1.trans (Nat.le_succ _)
    · intro receipt hr id hid
      simp only [failureDataStep, ChainState.freshId, List.mem_append, List.mem_singleton] at hr
      rcases hr with hold | rfl
      · exact (hp.2 receipt hold id hid).trans (Nat.lt_succ_self _)
      · simp only [Receipt.liveIds, List.mem_cons, List.not_mem_nil, or_false] at hid
        rcases hid with rfl | rfl
        · exact Nat.lt_succ_self _
        · exact ((houtputs output hm).trans_le hp.1).trans (Nat.lt_succ_self _)
  · exact ⟨Nat.le_refl _, by intro receipt hm; contradiction⟩

theorem Exec.addFailureData_outputIds (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (h : exec.OutputIdsBelowNext) (houtputs : ∀ output ∈ outputs, output.dataId < exec.state.nextId) :
    (exec.addFailureData receiver outputs).OutputIdsBelowNext := by
  have hf := failureDataFold_outputIds receiver outputs exec.state houtputs
  intro receipt hm id hid
  change receipt ∈ exec.newReceipts ++ (outputs.foldl (failureDataStep receiver) (exec.state, [])).2 at hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact (h receipt hold id hid).trans_le hf.1
  · exact hf.2 receipt hnew id hid

theorem completionDataFold_outputIds (receiver : AccountId) (data : Option Bytes) (outputs : List DataReceiver) (initial : ChainState)
    (houtputs : ∀ output ∈ outputs, output.dataId < initial.nextId) :
    let result := outputs.foldl (completionDataStep receiver data) (initial, [])
    initial.nextId ≤ result.1.nextId ∧
      ∀ receipt ∈ result.2, ∀ id ∈ receipt.liveIds, id < result.1.nextId := by
  apply foldl_preserves_mem (fun pair : ChainState × List Receipt => initial.nextId ≤ pair.1.nextId ∧
    ∀ receipt ∈ pair.2, ∀ id ∈ receipt.liveIds, id < pair.1.nextId)
  · intro pair output hm hp
    constructor
    · exact hp.1.trans (Nat.le_succ _)
    · intro receipt hr id hid
      simp only [completionDataStep, ChainState.freshId, List.mem_append, List.mem_singleton] at hr
      rcases hr with hold | rfl
      · exact (hp.2 receipt hold id hid).trans (Nat.lt_succ_self _)
      · simp only [Receipt.liveIds, List.mem_cons, List.not_mem_nil, or_false] at hid
        rcases hid with rfl | rfl
        · exact Nat.lt_succ_self _
        · exact ((houtputs output hm).trans_le hp.1).trans (Nat.lt_succ_self _)
  · exact ⟨Nat.le_refl _, by intro receipt hm; contradiction⟩

theorem Exec.addCompletionData_outputIds (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (h : exec.OutputIdsBelowNext) (houtputs : ∀ output ∈ outputs, output.dataId < exec.state.nextId) :
    (exec.addCompletionData receiver outputs).OutputIdsBelowNext := by
  unfold Exec.addCompletionData
  dsimp only
  split
  · exact h
  · rename_i data he
    have hf := completionDataFold_outputIds receiver data outputs exec.state houtputs
    intro receipt hm id hid
    change receipt ∈ exec.newReceipts ++ (outputs.foldl (completionDataStep receiver data) (exec.state, [])).2 at hm
    rcases List.mem_append.mp hm with hold | hnew
    · exact (h receipt hold id hid).trans_le hf.1
    · exact hf.2 receipt hnew id hid

theorem Exec.creditReceiptReward_outputIds (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (h : exec.OutputIdsBelowNext) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).OutputIdsBelowNext := by
  apply Exec.OutputIdsBelowNext.of_frame (before := exec)
    (after := exec.creditReceiptReward cfg receiver burnPrice purchasePrice) h
  · unfold Exec.creditReceiptReward
    split <;> rfl
  · exact Nat.le_of_eq (Exec.creditReceiptReward_nextId _ _ _ _ _).symm

/-- Finalization discards speculative receipts on failure before allocating
refunds and failed callback deliveries, all below the committed counter. -/
theorem finalizeReceipt_outputIds (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hraw : raw.OutputIdsBelowNext) (hmono : st.nextId ≤ raw.state.nextId)
    (hcallbacks : c.CallbackIdsBelow st.nextId) :
    (finalizeReceipt c st raw failed).OutputIdsBelowNext := by
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
  have hbase : base.OutputIdsBelowNext := by
    cases failed with
    | none => exact hraw
    | some error => intro receipt hm; contradiction
  have hnbase : st.nextId ≤ base.state.nextId := by
    cases failed <;> first | exact hmono | exact Nat.le_refl _
  have hcharged : charged.OutputIdsBelowNext := hbase
  have hbalance : balance.OutputIdsBelowNext := by
    dsimp only [balance]
    split
    · exact Exec.addBalanceRefund_outputIds charged _ _ hcharged
    · exact hcharged
  have hnbalance : st.nextId ≤ balance.state.nextId := by
    dsimp only [balance]
    split
    · exact hnbase.trans (Exec.addBalanceRefund_nextId_mono charged _ _)
    · exact hnbase
  have hgas : gas.OutputIdsBelowNext := by
    dsimp only [gas]
    split
    · exact Exec.addGasRefund_outputIds balance _ _ _ hbalance
    · exact hbalance
  have hngas : st.nextId ≤ gas.state.nextId := by
    dsimp only [gas]
    split
    · exact hnbalance.trans (Exec.addGasRefund_nextId_mono balance _ _ _)
    · exact hnbalance
  have hrewarded : rewarded.OutputIdsBelowNext :=
    Exec.creditReceiptReward_outputIds gas _ _ _ _ hgas
  have hnrewarded : st.nextId ≤ rewarded.state.nextId := by
    rw [Exec.creditReceiptReward_nextId]
    exact hngas
  have hfinished : finished.OutputIdsBelowNext := by
    dsimp only [finished]
    split
    · exact Exec.addFailureData_outputIds rewarded _ _ hrewarded
        (fun output hm => (hcallbacks output hm).trans_le hnrewarded)
    · exact Exec.addCompletionData_outputIds rewarded _ _ hrewarded
        (fun output hm => (hcallbacks output hm).trans_le hnrewarded)
  exact hfinished

theorem applyActionReceipt_outputIds (c : ReceiptCtx) (st : ChainState) (hcallbacks : c.CallbackIdsBelow st.nextId) :
    (applyActionReceipt c st).OutputIdsBelowNext :=
  finalizeReceipt_outputIds c st _ _ (runReceiptActions_outputIds c st hcallbacks)
    (runReceiptActions_nextId_mono c st) hcallbacks

end Near
