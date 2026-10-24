import NearRuntime.AccountDomainInvariant

namespace Near
open Wasm.Near

/-- Postponed receipt ownership using the broader financial actor scope.
Ordinary targets may be reserved; only system-origin refund shape is restricted. -/
structure ChainState.PostponedScopeWellFormed (st : ChainState) : Prop where
  unique : Assoc.KeysUnique st.postponed
  entries : ∀ id receipt, Assoc.lookup st.postponed id = some receipt →
    receipt.receiptId = id ∧ ∃ action, receipt.receipt = .action action ∧ ReceiptFinancialScope receipt
  yieldUnique : Assoc.KeysUnique st.yieldReceipts
  yieldEntries : ∀ key receipt, Assoc.lookup st.yieldReceipts key = some receipt →
    ∃ action, receipt.receipt = .action action ∧ ReceiptFinancialScope receipt

theorem ChainState.PostponedFinancialWellFormed.to_scope {st : ChainState}
    (h : st.PostponedFinancialWellFormed) : st.PostponedScopeWellFormed := by
  refine ⟨h.unique, ?_, h.yieldUnique, ?_⟩
  · intro id receipt hm
    obtain ⟨hid, action, ha, hs⟩ := h.entries id receipt hm
    exact ⟨hid, action, ha, ReceiptFinancialShape.to_scope receipt hs⟩
  · intro key receipt hm
    obtain ⟨action, ha, hs⟩ := h.yieldEntries key receipt hm
    exact ⟨action, ha, ReceiptFinancialShape.to_scope receipt hs⟩

/-- The postponed invariant depends only on the maps that own those receipts. -/
theorem ChainState.PostponedScopeWellFormed.of_postponed_eq {before after : ChainState}
    (hmap : after.postponed = before.postponed) (hyield : after.yieldReceipts = before.yieldReceipts)
    (h : before.PostponedScopeWellFormed) : after.PostponedScopeWellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hmap] using h.unique
  · intro id receipt hlookup
    exact h.entries id receipt (by simpa only [hmap] using hlookup)
  · simpa only [hyield] using h.yieldUnique
  · intro key receipt hlookup
    exact h.yieldEntries key receipt (by simpa only [hyield] using hlookup)

theorem ChainState.PostponedScopeWellFormed.empty (st : ChainState) (h : st.postponed = [])
    (hy : st.yieldReceipts = []) : st.PostponedScopeWellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Assoc.KeysUnique, h]
  · intro id receipt hlookup
    simp [h, Assoc.lookup] at hlookup
  · simp [Assoc.KeysUnique, hy]
  · intro key receipt hlookup
    simp [hy, Assoc.lookup] at hlookup

/-- Receipt insertion preserves id/payload agreement and financial action
scope. Freshness for monetary conservation remains a separate premise. -/
theorem postponeActionState_scopedWellFormed (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedScopeWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) :
    (postponeActionState st receipt action).PostponedScopeWellFormed := by
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
theorem releasePostponedState_scopedWellFormed (st : ChainState) (id : ReceiptId)
    (hwf : st.PostponedScopeWellFormed) :
    (releasePostponedState st id).PostponedScopeWellFormed := by
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
theorem yieldInsert_scopedWellFormed (st : ChainState) (key : AccountId × Bytes) (receipt : Receipt)
    (action : ActionReceipt) (hwf : st.PostponedScopeWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) :
    ({ st with yieldReceipts := Assoc.insert st.yieldReceipts key receipt } : ChainState).PostponedScopeWellFormed := by
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
theorem resumeYieldState_scopedWellFormed (st : ChainState) (key : AccountId × Bytes)
    (hwf : st.PostponedScopeWellFormed) : (resumeYieldState st key).PostponedScopeWellFormed := by
  refine ⟨hwf.unique, hwf.entries, hwf.yieldUnique.erase key, ?_⟩
  intro k candidate hlookup
  change Assoc.lookup (Assoc.erase st.yieldReceipts key) k = some candidate at hlookup
  by_cases he : key = k
  · subst k
    rw [Assoc.lookup_erase_self] at hlookup
    contradiction
  · rw [Assoc.lookup_erase_ne _ _ _ he] at hlookup
    exact hwf.yieldEntries k candidate hlookup

theorem processReceipt_action_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.PostponedScopeWellFormed) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
  cases hy : action.yieldDataId with
  | some dataId =>
    rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId haction hy]
    by_cases hs : (Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId)).isSome = true
    · simp only [hs, ite_true]; exact hwf
    · simp only [hs, Bool.false_eq_true, ite_false]
      exact yieldInsert_scopedWellFormed st _ receipt action hwf haction hshape
  | none =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | true =>
      have hq := processReceipt_ready_receiptQueues cfg ap decoder st receipt action haction hy he
      exact ChainState.PostponedScopeWellFormed.of_postponed_eq (congrArg Prod.fst hq)
        (congrArg (fun q => q.2.2) hq) hwf
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action haction hy he]
      exact postponeActionState_scopedWellFormed st receipt action hwf haction hshape

/-- Data delivery may erase and resume a stored action, or re-postpone it when
other inputs remain missing. Each real branch preserves the postponed invariant. -/
theorem processReceipt_data_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.PostponedScopeWellFormed) (hdata : receipt.receipt = .data data)
    (hplain : data.resumeDataId = none) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata hplain]
  cases hroute : Assoc.lookup st.postponedByData data.dataId with
  | none => exact ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl rfl hwf
  | some id =>
    simp only
    cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl rfl hwf
    | true =>
      simp only [ite_true]
      cases hwaiting : Assoc.lookup st.postponed id with
      | none => exact ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl rfl hwf
      | some waiting =>
        obtain ⟨_, action, ha, hshape⟩ := hwf.entries id waiting hwaiting
        exact processReceipt_action_scopedWellFormed cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action
          (releasePostponedState_scopedWellFormed _ id
            (ChainState.PostponedScopeWellFormed.of_postponed_eq (before := st) rfl rfl hwf)) ha hshape

theorem processReceipt_resume_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (data : DataReceipt) (dataId : Bytes)
    (hwf : st.PostponedScopeWellFormed) (hdata : receipt.receipt = .data data)
    (hres : data.resumeDataId = some dataId) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
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
      have hbase := resumeYieldState_scopedWellFormed st (receipt.receiverId, dataId) hwf
      have hq := runActionReceipt_receiptQueues cfg ap decoder (resumeYieldState st (receipt.receiverId, dataId)) y a
        [data.promiseResult]
      exact ChainState.PostponedScopeWellFormed.of_postponed_eq (congrArg Prod.fst hq)
        (congrArg (fun q => q.2.2) hq) hbase

/-- An incoming receipt in scope preserves postponed ownership even if the
processor returns a model issue. No accounting equation or success oracle is used. -/
theorem processReceipt_scopedWellFormed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.PostponedScopeWellFormed)
    (hshape : ReceiptFinancialScope receipt) :
    (processReceipt cfg ap decoder st receipt).state.PostponedScopeWellFormed := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_scopedWellFormed cfg ap decoder st receipt action hwf hr hshape
  | data data =>
    cases hres : data.resumeDataId with
    | none => exact processReceipt_data_scopedWellFormed cfg ap decoder st receipt data hwf hr hres
    | some dataId => exact processReceipt_resume_scopedWellFormed cfg ap decoder st receipt data dataId hwf hr hres
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    have hl := processDistribution_ledger cfg ap st receipt g
    unfold ChainState.ledgerState at hl
    simp only [Prod.mk.injEq] at hl
    exact ChainState.PostponedScopeWellFormed.of_postponed_eq hl.2.2.1 hl.2.2.2.2 hwf

/-- Running a stored receipt conserves the complete runtime-state ledger under the broader scope. -/
theorem runActionReceipt_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (results : List PromiseResult) (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent)
    (haction : receipt.receipt = .action action) (hshape : ReceiptFinancialScope receipt)
    (hnew : cfg.accountCostIncrease = true) (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (runActionReceipt cfg ap decoder st receipt action results).issue = none) :
    let processed := runActionReceipt cfg ap decoder st receipt action results
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  let ctx : ReceiptCtx :=
    { cfg, ap, receipt, action, promiseResults := results, codeOf := decoder
      vmYields := yieldsOf st receipt.receiverId }
  let exec := applyActionReceipt ctx st
  have hshape' : ActionReceiptFinancialScope receipt action := by simpa only [ReceiptFinancialScope, haction] using hshape
  have hf := applyActionReceipt_scope_conservation ctx st hwf hmissing haction hshape' hnew hratio
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

/-- Ready receipt processing conserves the complete runtime-state ledger,
including untouched postponed/delayed assets, new receipts, net burn and subsidy.
Both ordinary actions and constructor-shaped system refunds are covered. -/
theorem processReceipt_ready_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (haction : receipt.receipt = .action action)
    (hyield : action.yieldDataId = none)
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

/-- All actual action-receipt routing branches share one complete funding law.
The postponed identifier premise prevents overwriting a previously owned asset. -/
theorem processReceipt_action_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (haction : receipt.receipt = .action action)
    (hshape : ReceiptFinancialScope receipt) (hnew : cfg.accountCostIncrease = true)
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
    | true => exact processReceipt_ready_scope_conservation cfg ap decoder st receipt action hwf hmissing haction hy he hshape hnew hratio hsupported
    | false => exact processReceipt_waiting_conservation cfg ap decoder st receipt action haction hy he hunique hfresh

/-- Incoming data has zero value. Whether it only updates metadata or resumes
an action, the original postponed asset is counted exactly once. -/
theorem processReceipt_data_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (hdata : receipt.receipt = .data data)
    (hplain : data.resumeDataId = none)
    (hpost : st.PostponedScopeWellFormed) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata hplain] at hsupported ⊢
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
          (hpost.unique.erase id) hpost.yieldUnique hfresh hsupported
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

/-- Resuming a yield under the broader scope. -/
theorem processReceipt_resume_scope_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (data : DataReceipt) (dataId : Bytes)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) (hdata : receipt.receipt = .data data)
    (hres : data.resumeDataId = some dataId) (hpost : st.PostponedScopeWellFormed)
    (hnew : cfg.accountCostIncrease = true) (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  rw [processReceipt_resume cfg ap decoder st receipt data dataId hdata hres] at hsupported ⊢
  by_cases hmoot : (data.data.isNone &&
      Assoc.lookup st.yieldStatus (receipt.receiverId, dataId) == some YieldStatus.resumeInitiated) = true
  · simp only [hmoot, ite_true, Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil,
      List.sum_nil, Nat.add_zero, Nat.sub_zero, Fees.receiptFunds, hdata]
  · simp only [hmoot, Bool.false_eq_true, ite_false] at hsupported ⊢
    cases hy : Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) with
    | none =>
      simp only [hy, Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
        Nat.add_zero, Nat.sub_zero, Fees.receiptFunds, hdata]
    | some y =>
      simp only [hy] at hsupported ⊢
      obtain ⟨a, ha, hshape⟩ := hpost.yieldEntries _ y hy
      simp only [ha] at hsupported ⊢
      have hfunds := yieldErase_funds cfg st (receipt.receiverId, dataId) y hpost.yieldUnique hy
        (Assoc.erase st.yieldStatus (receipt.receiverId, dataId))
      have hrun := runActionReceipt_scope_conservation cfg ap decoder
        (resumeYieldState st (receipt.receiverId, dataId)) y a [data.promiseResult]
        (hwf.congr rfl rfl) hmissing ha hshape hnew hratio hsupported
      change (resumeYieldState st (receipt.receiverId, dataId)).totalFunds cfg + Fees.receiptFunds cfg y =
        st.totalFunds cfg at hfunds
      have hzero : Fees.receiptFunds cfg receipt = 0 := by simp [Fees.receiptFunds, hdata]
      dsimp only at hrun ⊢
      rw [hzero]
      omega

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
  | action action =>
    exact processReceipt_action_scope_conservation cfg ap decoder st receipt action hwf hmissing hr hshape hnew
      hratio hpost.unique hpost.yieldUnique hfresh hsupported
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      exact processReceipt_data_scope_conservation cfg ap decoder st receipt data hwf hmissing hr hres hpost hnew
        hratio hsupported
    | some dataId =>
      exact processReceipt_resume_scope_conservation cfg ap decoder st receipt data dataId hwf hmissing hr hres
        hpost hnew hratio hsupported
  | globalDistribution g => exact processReceipt_distribution_conservation cfg ap decoder st receipt g hr

end Near
