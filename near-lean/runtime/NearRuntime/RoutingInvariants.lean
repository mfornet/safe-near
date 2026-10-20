import NearRuntime.RoutingFunding

namespace Near
open Wasm.Near

/-- The postponed invariant depends only on the map that owns those receipts. -/
theorem ChainState.PostponedFinancialWellFormed.of_postponed_eq {before after : ChainState}
    (hmap : after.postponed = before.postponed) (h : before.PostponedFinancialWellFormed) :
    after.PostponedFinancialWellFormed := by
  constructor
  · simpa only [hmap] using h.unique
  · intro id receipt hlookup
    exact h.entries id receipt (by simpa only [hmap] using hlookup)

theorem ChainState.PostponedFinancialWellFormed.empty (st : ChainState) (h : st.postponed = []) :
    st.PostponedFinancialWellFormed := by
  constructor
  · simp [Assoc.KeysUnique, h]
  · intro id receipt hlookup
    simp [h, Assoc.lookup] at hlookup

/-- Receipt insertion preserves id/payload agreement and financial action
scope. Freshness for monetary conservation remains a separate premise. -/
theorem postponeActionState_postponedWellFormed (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedFinancialWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) :
    (postponeActionState st receipt action).PostponedFinancialWellFormed := by
  constructor
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
  constructor
  · exact hwf.unique.erase id
  · intro slot candidate hlookup
    change Assoc.lookup (Assoc.erase st.postponed id) slot = some candidate at hlookup
    by_cases he : id = slot
    · subst slot
      rw [Assoc.lookup_erase_self] at hlookup
      contradiction
    · rw [Assoc.lookup_erase_ne _ _ _ he] at hlookup
      exact hwf.entries slot candidate hlookup

/-- Ready execution and model-issue fallback both retain routing-owned queues;
this frame property does not assume the receipt actually committed. -/
theorem processReceipt_ready_receiptQueues (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true) :
    (processReceipt cfg ap decoder st receipt).state.receiptQueues = st.receiptQueues := by
  rw [processReceipt_ready cfg ap decoder st receipt action haction hready]
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
  cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
  | true =>
    apply ChainState.PostponedFinancialWellFormed.of_postponed_eq _ hwf
    exact congrArg Prod.fst (processReceipt_ready_receiptQueues cfg ap decoder st receipt action haction he)
  | false =>
    rw [processReceipt_waiting cfg ap decoder st receipt action haction he]
    exact postponeActionState_postponedWellFormed st receipt action hwf haction hshape

/-- Data delivery may erase and resume a stored action, or re-postpone it when
other inputs remain missing. Each real branch preserves the postponed invariant. -/
theorem processReceipt_data_postponedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.PostponedFinancialWellFormed) (hdata : receipt.receipt = .data data) :
    (processReceipt cfg ap decoder st receipt).state.PostponedFinancialWellFormed := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata]
  cases hroute : Assoc.lookup st.postponedByData data.dataId with
  | none => exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl hwf
  | some id =>
    simp only
    cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl hwf
    | true =>
      simp only [ite_true]
      cases hwaiting : Assoc.lookup st.postponed id with
      | none => exact ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl hwf
      | some waiting =>
        obtain ⟨_, action, ha, hshape⟩ := hwf.entries id waiting hwaiting
        exact processReceipt_action_postponedWellFormed cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action
          (releasePostponedState_postponedWellFormed _ id
            (ChainState.PostponedFinancialWellFormed.of_postponed_eq (before := st) rfl hwf)) ha hshape

/-- An incoming receipt in scope preserves postponed ownership even if the
processor returns a model issue. No accounting equation or success oracle is used. -/
theorem processReceipt_postponedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.PostponedFinancialWellFormed)
    (hshape : ReceiptFinancialShape receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedFinancialWellFormed := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_postponedWellFormed cfg ap decoder st receipt action hwf hr hshape
  | data data => exact processReceipt_data_postponedWellFormed cfg ap decoder st receipt data hwf hr

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
