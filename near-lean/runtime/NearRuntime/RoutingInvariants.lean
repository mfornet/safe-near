import NearRuntime.RoutingFunding

namespace Near
open Wasm.Near

/-- The postponed invariant depends only on the maps that own those receipts. -/
theorem ChainState.PostponedFinancialWellFormed.of_postponed_eq {before after : ChainState}
    (hmap : after.postponed = before.postponed) (hyield : after.yieldReceipts = before.yieldReceipts)
    (h : before.PostponedFinancialWellFormed) : after.PostponedFinancialWellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hmap] using h.unique
  · intro id receipt hlookup
    exact h.entries id receipt (by simpa only [hmap] using hlookup)
  · simpa only [hyield] using h.yieldUnique
  · intro key receipt hlookup
    exact h.yieldEntries key receipt (by simpa only [hyield] using hlookup)

theorem ChainState.PostponedFinancialWellFormed.empty (st : ChainState) (h : st.postponed = [])
    (hy : st.yieldReceipts = []) : st.PostponedFinancialWellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Assoc.KeysUnique, h]
  · intro id receipt hlookup
    simp [h, Assoc.lookup] at hlookup
  · simp [Assoc.KeysUnique, hy]
  · intro key receipt hlookup
    simp [hy, Assoc.lookup] at hlookup

/-- Receipt insertion preserves id/payload agreement and financial action
scope. Freshness for monetary conservation remains a separate premise. -/
theorem postponeActionState_postponedWellFormed (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedFinancialWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) :
    (postponeActionState st receipt action).PostponedFinancialWellFormed := by
  refine ⟨?_, ?_, hwf.yieldUnique, hwf.yieldEntries⟩
  · exact hwf.unique.insert _ _
  · intro id candidate hlookup
    change Assoc.lookup (Assoc.insert st.postponed receipt.receiptId receipt) id = some candidate at hlookup
    by_cases he : receipt.receiptId = id
    · subst id
      rw [Assoc.lookup_insert_self] at hlookup
      have hc := Option.some.inj hlookup
      subst candidate
      exact ⟨rfl, action, haction, hshape⟩
    · rw [Assoc.lookup_insert_ne _ _ _ _ he] at hlookup
      exact hwf.entries id candidate hlookup

/-- Removing a released receipt preserves the remaining map's structural scope. -/
theorem releasePostponedState_postponedWellFormed (st : ChainState) (id : ReceiptId)
    (hwf : st.PostponedFinancialWellFormed) :
    (releasePostponedState st id).PostponedFinancialWellFormed := by
  refine ⟨?_, ?_, hwf.yieldUnique, hwf.yieldEntries⟩
  · exact hwf.unique.erase id
  · intro slot candidate hlookup
    change Assoc.lookup (Assoc.erase st.postponed id) slot = some candidate at hlookup
    by_cases he : id = slot
    · subst slot
      rw [Assoc.lookup_erase_self] at hlookup
      contradiction
    · rw [Assoc.lookup_erase_ne _ _ _ he] at hlookup
      exact hwf.entries slot candidate hlookup

/-- Storing a yielded receipt under a fresh key. -/
theorem yieldInsert_postponedWellFormed (st : ChainState) (key : AccountId × Bytes) (receipt : Receipt)
    (action : ActionReceipt) (hwf : st.PostponedFinancialWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) :
    ({ st with yieldReceipts := Assoc.insert st.yieldReceipts key receipt } : ChainState).PostponedFinancialWellFormed := by
  refine ⟨hwf.unique, hwf.entries, hwf.yieldUnique.insert _ _, ?_⟩
  intro k candidate hlookup
  change Assoc.lookup (Assoc.insert st.yieldReceipts key receipt) k = some candidate at hlookup
  by_cases he : key = k
  · subst k
    rw [Assoc.lookup_insert_self] at hlookup
    have hc := Option.some.inj hlookup
    subst candidate
    exact ⟨action, haction, hshape⟩
  · rw [Assoc.lookup_insert_ne _ _ _ _ he] at hlookup
    exact hwf.yieldEntries k candidate hlookup

/-- Resuming removes a yield and its status. -/
theorem resumeYieldState_postponedWellFormed (st : ChainState) (key : AccountId × Bytes)
    (hwf : st.PostponedFinancialWellFormed) : (resumeYieldState st key).PostponedFinancialWellFormed := by
  refine ⟨hwf.unique, hwf.entries, hwf.yieldUnique.erase key, ?_⟩
  intro k candidate hlookup
  change Assoc.lookup (Assoc.erase st.yieldReceipts key) k = some candidate at hlookup
  by_cases he : key = k
  · subst k
    rw [Assoc.lookup_erase_self] at hlookup
    contradiction
  · rw [Assoc.lookup_erase_ne _ _ _ he] at hlookup
    exact hwf.yieldEntries k candidate hlookup

/-- Ready execution and model-issue fallback both retain routing-owned queues;
this frame property does not assume the receipt actually committed. -/
theorem processReceipt_ready_receiptQueues (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action) (hyield : action.yieldDataId = none)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true) :
    (processReceipt cfg ap decoder st receipt).state.receiptQueues = st.receiptQueues := by
  rw [processReceipt_ready cfg ap decoder st receipt action haction hyield hready]
  unfold processedOfExec
  split
  · rfl
  · have hf := applyActionReceipt_receiptQueues (readyActionContext cfg ap decoder st receipt action)
      (consumeReceiptDataState st action)
    exact hf

theorem processReceipt_action_postponedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedFinancialWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedFinancialWellFormed := by
  cases hy : action.yieldDataId with
  | some dataId =>
    rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId haction hy]
    by_cases hs : (Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId)).isSome = true
    · simp only [hs, ite_true]; exact hwf
    · simp only [hs, Bool.false_eq_true, ite_false]
      exact yieldInsert_postponedWellFormed st _ receipt action hwf haction hshape
  | none =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | true =>
      have hq := processReceipt_ready_receiptQueues cfg ap decoder st receipt action haction hy he
      exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (congrArg Prod.fst hq)
        (congrArg (fun q => q.2.2) hq) hwf
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action haction hy he]
      exact postponeActionState_postponedWellFormed st receipt action hwf haction hshape

/-- Data delivery may erase and resume a stored action, or re-postpone it when
other inputs remain missing. Each real branch preserves the postponed invariant. -/
theorem processReceipt_data_postponedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.PostponedFinancialWellFormed) (hdata : receipt.receipt = .data data)
    (hplain : data.resumeDataId = none) :
    (processReceipt cfg ap decoder st receipt).state.PostponedFinancialWellFormed := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata hplain]
  cases hroute : Assoc.lookup st.postponedByData data.dataId with
  | none => exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl rfl hwf
  | some id =>
    simp only
    cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl rfl hwf
    | true =>
      simp only [ite_true]
      cases hwaiting : Assoc.lookup st.postponed id with
      | none => exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl rfl hwf
      | some waiting =>
        obtain ⟨_, action, ha, hshape⟩ := hwf.entries id waiting hwaiting
        exact processReceipt_action_postponedWellFormed cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action
          (releasePostponedState_postponedWellFormed _ id
            (ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl rfl hwf)) ha hshape

/-- Resuming a yield runs the stored receipt; the routing-owned queues stay as the resume left them. -/
theorem processReceipt_resume_postponedWellFormed (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (data : DataReceipt) (dataId : Bytes)
    (hwf : st.PostponedFinancialWellFormed) (hdata : receipt.receipt = .data data)
    (hres : data.resumeDataId = some dataId) :
    (processReceipt cfg ap decoder st receipt).state.PostponedFinancialWellFormed := by
  rw [processReceipt_resume cfg ap decoder st receipt data dataId hdata hres]
  by_cases hmoot : (data.data.isNone &&
      Assoc.lookup st.yieldStatus (receipt.receiverId, dataId) == some YieldStatus.resumeInitiated) = true
  · simp only [hmoot, ite_true]; exact hwf
  · simp only [hmoot, Bool.false_eq_true, ite_false]
    cases hy : Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) with
    | none => exact hwf
    | some y =>
      simp only [hy]
      obtain ⟨a, ha, _⟩ := hwf.yieldEntries _ y hy
      simp only [ha]
      have hbase := resumeYieldState_postponedWellFormed st (receipt.receiverId, dataId) hwf
      have hq := runActionReceipt_receiptQueues cfg ap decoder (resumeYieldState st (receipt.receiverId, dataId)) y a
        [data.promiseResult]
      exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (congrArg Prod.fst hq)
        (congrArg (fun q => q.2.2) hq) hbase

/-- An incoming receipt in scope preserves postponed ownership even if the
processor returns a model issue. No accounting equation or success oracle is used. -/
theorem processReceipt_postponedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.PostponedFinancialWellFormed)
    (hshape : ReceiptFinancialShape receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedFinancialWellFormed := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_postponedWellFormed cfg ap decoder st receipt action hwf hr hshape
  | data data =>
    cases hres : data.resumeDataId with
    | none => exact processReceipt_data_postponedWellFormed cfg ap decoder st receipt data hwf hr hres
    | some dataId => exact processReceipt_resume_postponedWellFormed cfg ap decoder st receipt data dataId hwf hr hres
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    exact ChainState.postponedWellFormed_of_ledger (processDistribution_ledger cfg ap st receipt g) hwf

/-- Financial state premises preserved between supported receipt executions.
Full dependency validity, fresh external ids and future input scope are separate. -/
def ChainState.ReceiptFundingInvariant (st : ChainState) : Prop :=
  st.AccountsUnique ∧ st.PostponedFinancialWellFormed

theorem processReceipt_fundingInvariant (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.ReceiptFundingInvariant)
    (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.ReceiptFundingInvariant :=
  ⟨processReceipt_accountsUnique cfg ap decoder st receipt hwf.1 hwf.2 hshape hsupported,
    processReceipt_postponedWellFormed cfg ap decoder st receipt hwf.2 hshape⟩

end Near
