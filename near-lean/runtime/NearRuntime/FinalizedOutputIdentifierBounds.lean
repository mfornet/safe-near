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

theorem successDataFold_outputIds (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver) (initial : ChainState)
    (houtputs : ∀ output ∈ outputs, output.dataId < initial.nextId) :
    let result := outputs.foldl (successDataStep receiver bytes) (initial, [])
    initial.nextId ≤ result.1.nextId ∧
      ∀ receipt ∈ result.2, ∀ id ∈ receipt.liveIds, id < result.1.nextId := by
  apply foldl_preserves_mem (fun pair : ChainState × List Receipt => initial.nextId ≤ pair.1.nextId ∧
    ∀ receipt ∈ pair.2, ∀ id ∈ receipt.liveIds, id < pair.1.nextId)
  · intro pair output hm hp
    constructor
    · exact hp.1.trans (Nat.le_succ _)
    · intro receipt hr id hid
      simp only [successDataStep, ChainState.freshId, List.mem_append, List.mem_singleton] at hr
      rcases hr with hold | rfl
      · exact (hp.2 receipt hold id hid).trans (Nat.lt_succ_self _)
      · simp only [Receipt.liveIds, List.mem_cons, List.not_mem_nil, or_false] at hid
        rcases hid with rfl | rfl
        · exact Nat.lt_succ_self _
        · exact ((houtputs output hm).trans_le hp.1).trans (Nat.lt_succ_self _)
  · exact ⟨Nat.le_refl _, by intro receipt hm; contradiction⟩

theorem Exec.addSuccessData_outputIds (exec : Exec) (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (h : exec.OutputIdsBelowNext) (houtputs : ∀ output ∈ outputs, output.dataId < exec.state.nextId) :
    (exec.addSuccessData receiver outputs bytes).OutputIdsBelowNext := by
  have hf := successDataFold_outputIds receiver bytes outputs exec.state houtputs
  intro receipt hm id hid
  change receipt ∈ exec.newReceipts ++ (outputs.foldl (successDataStep receiver bytes) (exec.state, [])).2 at hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact (h receipt hold id hid).trans_le hf.1
  · exact hf.2 receipt hnew id hid

theorem Receipt.forwardResult_idsBelow (receipt : Receipt) (target : ReceiptId) (outputs : List DataReceiver)
    (bound : Nat) (h : ∀ id ∈ receipt.liveIds, id < bound)
    (houtputs : ∀ output ∈ outputs, output.dataId < bound) :
    ∀ id ∈ (receipt.forwardResult target outputs).liveIds, id < bound := by
  unfold Receipt.forwardResult
  split
  · cases hr : receipt.receipt with
    | data data => exact h
    | globalDistribution g => exact h
    | action action =>
      intro id hid
      simp only [Receipt.liveIds, List.map_append, List.mem_cons, List.mem_append] at hid
      rcases hid with he | hi | ho | hn
      · exact h id (by simp [Receipt.liveIds, hr, he])
      · exact h id (by simp [Receipt.liveIds, hr, hi])
      · exact h id (by simp [Receipt.liveIds, hr, ho])
      · obtain ⟨output, hm, rfl⟩ := List.mem_map.mp hn
        exact houtputs output hm
  · exact h

theorem Exec.forwardResult_outputIds (exec : Exec) (target : ReceiptId) (outputs : List DataReceiver)
    (h : exec.OutputIdsBelowNext) (houtputs : ∀ output ∈ outputs, output.dataId < exec.state.nextId) :
    (exec.forwardResult target outputs).OutputIdsBelowNext := by
  intro receipt hm
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hm
  exact Receipt.forwardResult_idsBelow original target outputs _ (h original horiginal) houtputs

theorem Exec.finishReceiptResult_outputIds (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError)
    (h : exec.OutputIdsBelowNext) (hcallbacks : c.CallbackIdsBelow exec.state.nextId) :
    (exec.finishReceiptResult c failed).OutputIdsBelowNext := by
  unfold Exec.finishReceiptResult
  split <;> unfold Exec.deliverResult <;> dsimp only <;> split
  all_goals first
    | exact Exec.addSuccessData_outputIds _ _ _ _ h hcallbacks
    | exact Exec.addFailureData_outputIds _ _ _ h hcallbacks
    | exact Exec.forwardResult_outputIds _ _ _ h hcallbacks

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
  let finished := rewarded.finishReceiptResult c failed
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
    exact Exec.finishReceiptResult_outputIds rewarded c failed hrewarded
      (fun output hm => (hcallbacks output hm).trans_le hnrewarded)
  exact hfinished

theorem applyActionReceipt_outputIds (c : ReceiptCtx) (st : ChainState) (hcallbacks : c.CallbackIdsBelow st.nextId) :
    (applyActionReceipt c st).OutputIdsBelowNext :=
  finalizeReceipt_outputIds c st _ _ (runReceiptActions_outputIds c st hcallbacks)
    (runReceiptActions_nextId_mono c st) hcallbacks

end Near
