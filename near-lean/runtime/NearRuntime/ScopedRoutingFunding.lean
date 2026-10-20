import NearRuntime.AccountDomainInvariant

namespace Near
open Wasm.Near

/-- Postponed receipt ownership using the broader financial actor scope.
Ordinary targets may be reserved; only system-origin refund shape is restricted. -/
structure ChainState.PostponedScopeWellFormed (st : ChainState) : Prop where
  unique : Assoc.KeysUnique st.postponed
  entries : ∀ id receipt, Assoc.lookup st.postponed id = some receipt →
    receipt.receiptId = id ∧ ∃ action, receipt.receipt = .action action ∧ ReceiptFinancialScope receipt

theorem ChainState.PostponedFinancialWellFormed.to_scope {st : ChainState}
    (h : st.PostponedFinancialWellFormed) : st.PostponedScopeWellFormed := by
  constructor
  · exact h.unique
  · intro id receipt hm
    obtain ⟨hid, action, ha, hs⟩ := h.entries id receipt hm
    exact ⟨hid, action, ha, ReceiptFinancialShape.to_scope receipt hs⟩

/-- The postponed invariant depends only on the map that owns those receipts. -/
theorem ChainState.PostponedScopeWellFormed.of_postponed_eq {before after : ChainState}
    (hmap : after.postponed = before.postponed) (h : before.PostponedScopeWellFormed) :
    after.PostponedScopeWellFormed := by
  constructor
  · simpa only [hmap] using h.unique
  · intro id receipt hlookup
    exact h.entries id receipt (by simpa only [hmap] using hlookup)

theorem ChainState.PostponedScopeWellFormed.empty (st : ChainState) (h : st.postponed = []) :
    st.PostponedScopeWellFormed := by
  constructor
  · simp [Assoc.KeysUnique, h]
  · intro id receipt hlookup
    simp [h, Assoc.lookup] at hlookup

/-- Receipt insertion preserves id/payload agreement and financial action
scope. Freshness for monetary conservation remains a separate premise. -/
theorem postponeActionState_scopedWellFormed (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedScopeWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) :
    (postponeActionState st receipt action).PostponedScopeWellFormed := by
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
theorem releasePostponedState_scopedWellFormed (st : ChainState) (id : ReceiptId)
    (hwf : st.PostponedScopeWellFormed) :
    (releasePostponedState st id).PostponedScopeWellFormed := by
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

theorem processReceipt_action_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedScopeWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
  cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
  | true =>
    apply ChainState.PostponedScopeWellFormed.of_postponed_eq _ hwf
    exact congrArg Prod.fst (processReceipt_ready_receiptQueues cfg ap decoder st receipt action haction he)
  | false =>
    rw [processReceipt_waiting cfg ap decoder st receipt action haction he]
    exact postponeActionState_scopedWellFormed st receipt action hwf haction hshape

/-- Data delivery may erase and resume a stored action, or re-postpone it when
other inputs remain missing. Each real branch preserves the postponed invariant. -/
theorem processReceipt_data_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.PostponedScopeWellFormed) (hdata : receipt.receipt = .data data) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata]
  cases hroute : Assoc.lookup st.postponedByData data.dataId with
  | none => exact ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl hwf
  | some id =>
    simp only
    cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl hwf
    | true =>
      simp only [ite_true]
      cases hwaiting : Assoc.lookup st.postponed id with
      | none => exact ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl hwf
      | some waiting =>
        obtain ⟨_, action, ha, hshape⟩ := hwf.entries id waiting hwaiting
        exact processReceipt_action_scopedWellFormed cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action
          (releasePostponedState_scopedWellFormed _ id
            (ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl hwf)) ha hshape

/-- An incoming receipt in scope preserves postponed ownership even if the
processor returns a model issue. No accounting equation or success oracle is used. -/
theorem processReceipt_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.PostponedScopeWellFormed)
    (hshape : ReceiptFinancialScope receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_scopedWellFormed cfg ap decoder st receipt action hwf hr hshape
  | data data => exact processReceipt_data_scopedWellFormed cfg ap decoder st receipt data hwf hr

/-- Ready receipt processing conserves the complete runtime-state ledger,
including untouched postponed/delayed assets, new receipts, net burn and subsidy.
Both ordinary actions and constructor-shaped system refunds are covered. -/
theorem processReceipt_ready_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (haction : receipt.receipt = .action action)
    (hready : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true)
    (hshape : ReceiptFinancialScope receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  let before := consumeReceiptDataState st action
  let ctx := readyActionContext cfg ap decoder st receipt action
  let exec := applyActionReceipt ctx before
  have hshape' : ActionReceiptFinancialScope receipt action := by simpa only [ReceiptFinancialScope, haction] using hshape
  have hf := applyActionReceipt_scope_conservation ctx before hwf hmissing haction hshape' hnew hratio
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

/-- Both actual action-receipt routing branches share one complete funding law.
The postponed identifier premise prevents overwriting a previously owned asset. -/
theorem processReceipt_action_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hunique : Assoc.KeysUnique st.postponed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
  | true => exact processReceipt_ready_scope_conservation cfg ap decoder st receipt action hwf hmissing haction he hshape hnew hratio hsupported
  | false => exact processReceipt_waiting_conservation cfg ap decoder st receipt action haction he hunique hfresh

/-- Incoming data has zero value. Whether it only updates metadata or resumes
an action, the original postponed asset is counted exactly once. -/
theorem processReceipt_data_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (hdata : receipt.receipt = .data data)
    (hpost : st.PostponedScopeWellFormed) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata] at hsupported ⊢
  cases hroute : Assoc.lookup st.postponedByData data.dataId with
  | none =>
    simp only [Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
      Nat.add_zero, Nat.sub_zero, Fees.receiptFunds, hdata]
    rfl
  | some id =>
    simp only [hroute] at hsupported ⊢
    cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
    | true =>
      simp only [hpending, ite_true] at hsupported ⊢
      cases hwaiting : Assoc.lookup st.postponed id with
      | none =>
        simp only [Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
          Nat.add_zero, Nat.sub_zero, Fees.receiptFunds, hdata]
        rfl
      | some waiting =>
        simp only [hwaiting] at hsupported ⊢
        obtain ⟨hid, action, ha, hshape⟩ := hpost.entries id waiting hwaiting
        have hfresh : Assoc.lookup (releasePostponedState (receivePostponedDataState st data) id).postponed waiting.receiptId = none := by
          rw [hid]
          exact Assoc.lookup_erase_self _ _
        have hf := processReceipt_action_scope_conservation cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action hwf hmissing ha hshape hnew hratio
          (hpost.unique.erase id) hfresh hsupported
        have hreleased := releasePostponedState_funds cfg (receivePostponedDataState st data) id waiting hpost.unique hwaiting
        change (releasePostponedState (receivePostponedDataState st data) id).totalFunds cfg +
          Fees.receiptFunds cfg waiting = st.totalFunds cfg at hreleased
        dsimp only at hf ⊢
        rw [hreleased] at hf
        simpa only [Fees.receiptFunds, hdata, Nat.add_zero] using hf
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      simp only [Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
        Nat.add_zero, Nat.sub_zero, Fees.receiptFunds, hdata]
      rfl

/-- Financially scoped supported receipt processing conserves accounts, delayed and
postponed backing, outgoing receipts, net burn and explicit subsidy. Preconditions
are structural ids/receipt scope and protocol configuration; no accounting or VM
result equation is supplied by the caller. -/
theorem processReceipt_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent)
    (hpost : st.PostponedScopeWellFormed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none)
    (hshape : ReceiptFinancialScope receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_scope_conservation cfg ap decoder st receipt action hwf hmissing hr hshape hnew hratio hpost.unique hfresh hsupported
  | data data => exact processReceipt_data_scope_conservation cfg ap decoder st receipt data hwf hmissing hr hpost hnew hratio hsupported


end Near
