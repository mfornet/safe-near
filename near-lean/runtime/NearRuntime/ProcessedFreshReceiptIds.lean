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
  let base := rollbackReceipt st raw failed
  let settlement := Fees.settleGas c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) base.gasUsed base.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (base.state.account? c.receipt.receiverId).isSome && failed.isNone)
  let charged := { base with
    tokensBurnt := (if c.receipt.isRefund then 0 else settlement.tokensBurnt) + base.actionTokensBurnt
    otherTokensBurnt := if c.receipt.isRefund && failed.isSome then Fees.totalDeposit c.action.actions else 0 }
  let depositRefund := if failed.isSome then Fees.totalDeposit c.action.actions else 0
  let gasRefund := if c.receipt.isRefund then 0 else settlement.refund
  let balance := if depositRefund > 0 && c.receipt.predecessorId != systemAccount then
    charged.addBalanceRefund c.receipt.predecessorId depositRefund else charged
  let gas := if gasRefund > 0 && c.action.signerId != systemAccount then
    balance.addGasRefund c.action.signerId c.action.signerPublicKey gasRefund else balance
  let rewarded := gas.creditReceiptReward c.cfg c.receipt.receiverId settlement.burnPrice c.action.gasPrice
  let finished := rewarded.finishReceiptResult c failed
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
    exact Exec.finishReceiptResult_freshIds rewarded c failed _ hrewarded hnrewarded
  exact hfinished

theorem applyActionReceipt_freshIds (c : ReceiptCtx) (st : ChainState) :
    (applyActionReceipt c st).FreshReceiptIds st.nextId :=
  finalizeReceipt_freshIds c st _ _ (runReceiptActions_freshIds c st) (runReceiptActions_nextId_mono c st)

theorem processDistribution_freshIds (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) :
    ReceiptList.FreshIds st.nextId (processDistribution cfg ap st r g).state.nextId
      (processDistribution cfg ap st r g).receipts := by
  unfold processDistribution
  dsimp only
  repeat' (first
    | exact ReceiptList.FreshIds.empty _ _
    | (constructor
       · simp
       · intro receipt hm
         have he := List.mem_singleton.mp hm
         subst receipt
         exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩)
    | split)

/-- Public receipt outputs are collision-free and newly allocated, without any
validity, financial-scope, input-bound or successful-execution assumption. -/
theorem processReceipt_freshIds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) :
    ReceiptList.FreshIds st.nextId (processReceipt cfg ap decoder st receipt).state.nextId
      (processReceipt cfg ap decoder st receipt).receipts := by
  cases hr : receipt.receipt with
  | action action =>
    cases hy : action.yieldDataId with
    | some dataId =>
      rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId hr hy]
      split <;> exact ReceiptList.FreshIds.empty _ _
    | none =>
      cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
      | false =>
        rw [processReceipt_waiting cfg ap decoder st receipt action hr hy he]
        exact ReceiptList.FreshIds.empty _ _
      | true =>
        rw [processReceipt_ready cfg ap decoder st receipt action hr hy he]
        unfold processedOfExec
        split
        · exact ReceiptList.FreshIds.empty _ _
        · exact applyActionReceipt_freshIds (readyActionContext cfg ap decoder st receipt action)
            (consumeReceiptDataState st action)
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
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
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · exact ReceiptList.FreshIds.empty _ _
      · split
        · rename_i y _
          split
          · rename_i a _
            rw [runActionReceipt_eq]
            unfold processedOfExec
            split
            · exact ReceiptList.FreshIds.empty _ _
            · exact applyActionReceipt_freshIds _ _
          · exact ReceiptList.FreshIds.empty _ _
        · exact ReceiptList.FreshIds.empty _ _
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    exact processDistribution_freshIds cfg ap st receipt g
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

theorem ReceiptList.FreshIds.subperm {lower upper : Nat} {E l : List Receipt}
    (h : ReceiptList.FreshIds lower upper E) (hl : l.Subperm E) : ReceiptList.FreshIds lower upper l := by
  constructor
  · exact (hl.map _).nodup_of_subperm h.unique
  · intro receipt hm
    exact h.bounds receipt (hl.subset hm)

/-- A receipt and the instant receipts it creates: the non-instant receipts sent out use distinct
fresh ids from the interval the whole run consumed. -/
theorem processWithInstants_freshIds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) :
    ReceiptList.FreshIds st.nextId (processWithInstants cfg ap decoder st receipt).state.nextId
      (processWithInstants cfg ap decoder st receipt).receipts := by
  have key := processWithInstants_induction cfg ap decoder
    (fun acc pending => st.nextId ≤ acc.state.nextId ∧ ∃ E : List Receipt,
      ReceiptList.FreshIds st.nextId acc.state.nextId E ∧ (acc.receipts ++ pending).Subperm E)
    (fun p => ReceiptList.FreshIds st.nextId p.state.nextId p.receipts)
    (fun st' _ => st' = st)
    (by
      intro acc h
      obtain ⟨_, E, hE, hs⟩ := h
      exact hE.subperm (by simpa using hs))
    (by
      intro acc pending issue _ h
      obtain ⟨_, E, hE, hs⟩ := h
      exact hE.subperm ((List.sublist_append_left _ _).subperm.trans hs))
    (by
      intro acc r rest h hs hi
      obtain ⟨hlow, E, hE, hsub⟩ := h
      have hn := processReceipt_nextId_mono cfg { ap with storageAccounting := acc.storageAccounting } decoder
        acc.state r
      have hf := processReceipt_freshIds cfg { ap with storageAccounting := acc.storageAccounting } decoder acc.state r
      change st.nextId ≤ (instantStep cfg ap decoder acc r).state.nextId ∧ ∃ E' : List Receipt,
        ReceiptList.FreshIds st.nextId (instantStep cfg ap decoder acc r).state.nextId E' ∧
          ((instantAccumulate acc (instantStep cfg ap decoder acc r)).receipts ++
            (rest ++ (instantStep cfg ap decoder acc r).receipts.filter Receipt.isInstant)).Subperm E'
      refine ⟨hlow.trans hn, E ++ (instantStep cfg ap decoder acc r).receipts,
        ReceiptList.FreshIds.append hE hf hlow hn, ?_⟩
      have hperm : ((instantAccumulate acc (instantStep cfg ap decoder acc r)).receipts ++
          (rest ++ (instantStep cfg ap decoder acc r).receipts.filter Receipt.isInstant)).Perm
          ((acc.receipts ++ rest) ++ ((instantStep cfg ap decoder acc r).receipts.filter Receipt.isInstant ++
            (instantStep cfg ap decoder acc r).receipts.filter fun x => !x.isInstant)) := by
        simp only [instantAccumulate, Processed.append_receipts, List.append_assoc]
        refine List.Perm.append_left _ ?_
        refine (List.perm_append_comm_assoc _ _ _).trans ?_
        exact List.Perm.append_left _ List.perm_append_comm
      refine hperm.subperm.trans (List.Subperm.append ?_ ?_)
      · exact ((List.Sublist.append_left (List.sublist_cons_self r rest) _).subperm).trans hsub
      · exact (List.filter_append_perm _ _).subperm)
    (by
      rintro st' r' rfl hne
      exact processReceipt_freshIds cfg ap decoder st r')
    (by
      rintro st' r' rfl hi
      have hn := processReceipt_nextId_mono cfg ap decoder st r'
      have hf := processReceipt_freshIds cfg ap decoder st r'
      refine ⟨hn, (processReceipt cfg ap decoder st r').receipts, hf, ?_⟩
      exact (List.perm_append_comm.trans (List.filter_append_perm Receipt.isInstant _)).subperm)
  exact key st receipt rfl

end Near
