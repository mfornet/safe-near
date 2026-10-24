import NearRuntime.FreshReceiptIds
import NearRuntime.FinalizeStages

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

theorem successDataFold_freshIds (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver) (initial : ChainState) :
    let result := outputs.foldl (successDataStep receiver bytes) (initial, [])
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

theorem Exec.addSuccessData_freshIds (exec : Exec) (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver) (lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.addSuccessData receiver outputs bytes).FreshReceiptIds lower := by
  have hf := successDataFold_freshIds receiver bytes outputs exec.state
  exact ReceiptList.FreshIds.append h hf.2 hfloor hf.1

@[simp] theorem Receipt.forwardResult_receiptId (receipt : Receipt) (target : ReceiptId) (outputs : List DataReceiver) :
    (receipt.forwardResult target outputs).receiptId = receipt.receiptId := by
  unfold Receipt.forwardResult
  split
  · cases receipt.receipt <;> rfl
  · rfl

theorem Exec.forwardResult_freshIds (exec : Exec) (target : ReceiptId) (outputs : List DataReceiver) (lower : Nat)
    (h : exec.FreshReceiptIds lower) : (exec.forwardResult target outputs).FreshReceiptIds lower := by
  constructor
  · simpa only [Exec.forwardResult, List.map_map, Function.comp_def, Receipt.forwardResult_receiptId] using h.unique
  · intro receipt hm
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hm
    simpa only [Exec.forwardResult, Receipt.forwardResult_receiptId] using h.bounds original horiginal

theorem Exec.finishReceiptResult_freshIds (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError) (lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.finishReceiptResult c failed).FreshReceiptIds lower := by
  unfold Exec.finishReceiptResult
  split <;> unfold Exec.deliverResult <;> dsimp only <;> split
  all_goals first
    | exact Exec.addSuccessData_freshIds _ _ _ _ _ h hfloor
    | exact Exec.addFailureData_freshIds _ _ _ _ h hfloor
    | exact Exec.forwardResult_freshIds _ _ _ _ h

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
  -- Each stage allocates above the counter, which never moves back.
  refine (finalizeReceipt_stages (fun e => e.FreshReceiptIds st.nextId ∧ st.nextId ≤ e.state.nextId)
    c st raw failed ?_
    (fun _ _ _ h => h)
    (fun e _ _ h => ⟨Exec.addBalanceRefund_freshIds e _ _ _ h.1 h.2,
      h.2.trans (Exec.addBalanceRefund_nextId_mono e _ _)⟩)
    (fun e _ _ _ h => ⟨Exec.addGasRefund_freshIds e _ _ _ _ h.1 h.2,
      h.2.trans (Exec.addGasRefund_nextId_mono e _ _ _)⟩)
    (fun e _ _ h => ⟨Exec.creditReceiptReward_freshIds e _ _ _ _ _ h.1,
      by rw [Exec.creditReceiptReward_nextId]; exact h.2⟩)
    (fun e h => ⟨Exec.finishReceiptResult_freshIds e c failed _ h.1 h.2,
      h.2.trans (Exec.finishReceiptResult_nextId_mono e c failed)⟩)
    (fun _ _ h => h)).1
  cases failed with
  | none => exact ⟨hraw, hmono⟩
  | some error => exact ⟨ReceiptList.FreshIds.empty _ _, Nat.le_refl _⟩

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
