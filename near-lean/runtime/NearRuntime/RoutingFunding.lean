import NearRuntime.ProcessedFunding

namespace Near
open Wasm.Near

/-- Financially relevant postponed-map structure. This is not full dependency-
graph validity or fairness: ids are unique, match their payloads, and contain
financially scoped action receipts. Yielded receipts are held under unique keys and are
financially scoped action receipts too. -/
structure ChainState.PostponedFinancialWellFormed (st : ChainState) : Prop where
  unique : Assoc.KeysUnique st.postponed
  entries : ∀ id receipt, Assoc.lookup st.postponed id = some receipt →
    receipt.receiptId = id ∧ ∃ action, receipt.receipt = .action action ∧ ReceiptFinancialShape receipt
  yieldUnique : Assoc.KeysUnique st.yieldReceipts
  yieldEntries : ∀ key receipt, Assoc.lookup st.yieldReceipts key = some receipt →
    ∃ action, receipt.receipt = .action action ∧ ReceiptFinancialShape receipt

theorem Assoc.lookup_erase_self {κ α : Type} [BEq κ] [LawfulBEq κ] (map : List (κ × α)) (key : κ) :
    Assoc.lookup (Assoc.erase map key) key = none := by
  apply Assoc.lookup_none_of_key_not_mem
  rw [Assoc.keys_erase]
  simp

/-- The first data-arrival update changes only zero-value routing metadata. -/
def receivePostponedDataState (st : ChainState) (data : DataReceipt) : ChainState :=
  { st with
    receivedData := Assoc.insert st.receivedData data.dataId data.data
    postponedByData := Assoc.erase st.postponedByData data.dataId }

/-- Executable unfolding of data routing. A released action receipt is passed
back to the same real processor after its old queue entry has been removed. -/
theorem processReceipt_data (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt) (hdata : receipt.receipt = .data data)
    (hplain : data.resumeDataId = none) :
    processReceipt cfg ap decoder st receipt =
      match Assoc.lookup st.postponedByData data.dataId with
      | none => { state := { st with receivedData := Assoc.insert st.receivedData data.dataId data.data }, storageAccounting := ap.storageAccounting }
      | some id =>
        let received := receivePostponedDataState st data
        let pending := (Assoc.lookup st.pendingDataCount id).getD 1 - 1
        if pending == 0 then
          match Assoc.lookup st.postponed id with
          | none => { state := received, storageAccounting := ap.storageAccounting }
          | some waiting => processReceipt cfg ap decoder (releasePostponedState received id) waiting
        else { state := { received with pendingDataCount := Assoc.insert received.pendingDataCount id pending }, storageAccounting := ap.storageAccounting } := by
  rw [processReceipt]
  simp only [hdata, hplain]
  repeat' (first | rfl | contradiction | split)
  all_goals simp_all [receivePostponedDataState, releasePostponedState]

/-- The outcome of the promise a resumed or timed-out yield waits for. -/
def DataReceipt.promiseResult (data : DataReceipt) : Wasm.PromiseResult :=
  match data.data with
  | some bytes => Wasm.PromiseResult.successful bytes
  | none => Wasm.PromiseResult.failed

/-- The yield table without the entry a resume consumed. -/
def resumeYieldState (st : ChainState) (key : AccountId × Bytes) : ChainState :=
  { st with yieldReceipts := Assoc.erase st.yieldReceipts key, yieldStatus := Assoc.erase st.yieldStatus key }

/-- Executable unfolding of a resume (or a yield timeout): the stored receipt runs with the
resume payload as its promise result, unless the timeout of an already resumed yield arrives. -/
theorem processReceipt_resume (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt) (dataId : Bytes)
    (hdata : receipt.receipt = .data data) (hres : data.resumeDataId = some dataId) :
    processReceipt cfg ap decoder st receipt =
      if data.data.isNone && Assoc.lookup st.yieldStatus (receipt.receiverId, dataId) == some YieldStatus.resumeInitiated then
        { state := st, storageAccounting := ap.storageAccounting }
      else
        match Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) with
        | some y =>
          match y.receipt with
          | .action a =>
            runActionReceipt cfg ap decoder (resumeYieldState st (receipt.receiverId, dataId)) y a [data.promiseResult]
          | _ => { state := resumeYieldState st (receipt.receiverId, dataId), storageAccounting := ap.storageAccounting }
        | none => { state := st, storageAccounting := ap.storageAccounting } := by
  rw [processReceipt]
  simp only [hdata, hres]
  by_cases hmoot : (data.data.isNone &&
      Assoc.lookup st.yieldStatus (receipt.receiverId, dataId) == some YieldStatus.resumeInitiated) = true
  · simp only [hmoot, ite_true]
  · simp only [hmoot, Bool.false_eq_true, ite_false]
    cases h : Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) with
    | none => rfl
    | some y =>
      cases hy : y.receipt with
      | action a => rfl
      | data _ => rfl
      | globalDistribution _ => rfl

/-- Incoming data has zero value. Whether it only updates metadata or resumes
an action, the original postponed asset is counted exactly once. -/
theorem processReceipt_data_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.AccountsUnique) (hdata : receipt.receipt = .data data) (hplain : data.resumeDataId = none)
    (hpost : st.PostponedFinancialWellFormed) (hnew : cfg.accountCostIncrease = true)
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
        have hf := processReceipt_action_conservation cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action hwf ha hshape hnew hratio
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

/-- Resuming a yield moves its stored receipt's backing into the execution, which conserves funds
like any other receipt; a moot timeout or a vanished yield changes nothing. -/
theorem processReceipt_resume_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt) (dataId : Bytes)
    (hwf : st.AccountsUnique) (hdata : receipt.receipt = .data data) (hres : data.resumeDataId = some dataId)
    (hpost : st.PostponedFinancialWellFormed) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
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
      simp only [Processed.totalFunds, Processed.netTokensBurnt, receiptsFunds, List.map_nil, List.sum_nil,
        Nat.add_zero, Nat.sub_zero, Fees.receiptFunds, hdata]
    | some y =>
      simp only [hy] at hsupported ⊢
      obtain ⟨a, ha, hshape⟩ := hpost.yieldEntries _ y hy
      simp only [ha] at hsupported ⊢
      have hfunds := yieldErase_funds cfg st (receipt.receiverId, dataId) y hpost.yieldUnique hy
        (Assoc.erase st.yieldStatus (receipt.receiverId, dataId))
      have hrun := runActionReceipt_conservation cfg ap decoder
        (resumeYieldState st (receipt.receiverId, dataId)) y a [data.promiseResult]
        (hwf.congr rfl rfl) ha hshape hnew hratio hsupported
      change (resumeYieldState st (receipt.receiverId, dataId)).totalFunds cfg + Fees.receiptFunds cfg y =
        st.totalFunds cfg at hfunds
      have hzero : Fees.receiptFunds cfg receipt = 0 := by simp [Fees.receiptFunds, hdata]
      dsimp only at hrun ⊢
      rw [hzero]
      omega

/-- The funds of a state depend only on its accounts, keys and queued receipts. -/
def ChainState.ledgerState (st : ChainState) :=
  (st.accounts, st.accessKeys, st.postponed, st.delayed, st.yieldReceipts)

theorem ChainState.totalFunds_of_ledger {a b : ChainState} (cfg : RuntimeConfig)
    (h : a.ledgerState = b.ledgerState) : a.totalFunds cfg = b.totalFunds cfg := by
  unfold ChainState.ledgerState at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold ChainState.totalFunds ChainState.queuedFunds ChainState.postponedFunds ChainState.yieldFunds
  rw [ChainState.totalBalance_congr h1 h2, h3, h4, h5]

theorem ChainState.accountsUnique_of_ledger {a b : ChainState} (h : a.ledgerState = b.ledgerState)
    (hwf : b.AccountsUnique) : a.AccountsUnique := by
  unfold ChainState.ledgerState at h
  simp only [Prod.mk.injEq] at h
  exact hwf.congr h.1.symm h.2.1.symm

theorem ChainState.postponedWellFormed_of_ledger {a b : ChainState} (h : a.ledgerState = b.ledgerState)
    (hwf : b.PostponedFinancialWellFormed) : a.PostponedFinancialWellFormed := by
  unfold ChainState.ledgerState at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨_, _, h3, _, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [h3] using hwf.unique
  · intro id receipt hlookup
    exact hwf.entries id receipt (by simpa only [h3] using hlookup)
  · simpa only [h5] using hwf.yieldUnique
  · intro key receipt hlookup
    exact hwf.yieldEntries key receipt (by simpa only [h5] using hlookup)

/-- Applying a global contract distribution changes only global code, nonces and the allocator. -/
theorem processDistribution_ledger (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) :
    (processDistribution cfg ap st r g).state.ledgerState = st.ledgerState := by
  unfold processDistribution
  dsimp only
  repeat' (first | rfl | split)

theorem processDistribution_advance (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) : st.RoutingAdvance (processDistribution cfg ap st r g).state := by
  unfold processDistribution
  dsimp only
  repeat' (first
    | exact ChainState.RoutingAdvance.refl _
    | exact ChainState.RoutingAdvance.of_routing rfl
    | exact (ChainState.RoutingAdvance.of_routing rfl).trans (ChainState.RoutingAdvance.freshId _)
    | split)

theorem processDistribution_funds (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) :
    (processDistribution cfg ap st r g).receipts.map (Fees.receiptFunds cfg) =
      (processDistribution cfg ap st r g).receipts.map (fun _ => 0) := by
  unfold processDistribution
  dsimp only
  repeat' (first | rfl | split)

theorem processDistribution_outcomes (cfg : RuntimeConfig) (ap : ApplyState) (st : ChainState) (r : Receipt)
    (g : GlobalDistribution) :
    (processDistribution cfg ap st r g).outcomes = [] ∧ (processDistribution cfg ap st r g).otherTokensBurnt = 0 ∧
      (processDistribution cfg ap st r g).rewards = 0 ∧ (processDistribution cfg ap st r g).subsidizedAmount = 0 := by
  unfold processDistribution
  dsimp only
  repeat' (first | exact ⟨rfl, rfl, rfl, rfl⟩ | split)

theorem processReceipt_distribution (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (g : GlobalDistribution)
    (hr : receipt.receipt = .globalDistribution g) :
    processReceipt cfg ap decoder st receipt = processDistribution cfg ap st receipt g := by
  rw [processReceipt]
  simp only [hr]

/-- A distribution receipt carries no funds and moves none. -/
theorem processReceipt_distribution_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (g : GlobalDistribution)
    (hr : receipt.receipt = .globalDistribution g) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  rw [processReceipt_distribution cfg ap decoder st receipt g hr]
  obtain ⟨ho, hb, hw, hs⟩ := processDistribution_outcomes cfg ap st receipt g
  have hl := ChainState.totalFunds_of_ledger cfg (processDistribution_ledger cfg ap st receipt g)
  have hf := processDistribution_funds cfg ap st receipt g
  have hzero : Fees.receiptFunds cfg receipt = 0 := by simp [Fees.receiptFunds, hr]
  have hsum : receiptsFunds cfg (processDistribution cfg ap st receipt g).receipts = 0 := by
    unfold receiptsFunds
    rw [hf]
    simp
  dsimp only [Processed.totalFunds, Processed.netTokensBurnt]
  rw [hsum, ho, hb, hw, hs, hzero, hl]
  simp

/-- Financially scoped supported receipt processing conserves accounts, delayed and
postponed backing, outgoing receipts, net burn and explicit subsidy. Preconditions
are structural ids/receipt scope and protocol configuration; no accounting or VM
result equation is supplied by the caller. -/
theorem processReceipt_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.AccountsUnique)
    (hpost : st.PostponedFinancialWellFormed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  cases hr : receipt.receipt with
  | action action =>
    exact processReceipt_action_conservation cfg ap decoder st receipt action hwf hr hshape hnew hratio
      hpost.unique hpost.yieldUnique hfresh hsupported
  | data data =>
    cases hres : data.resumeDataId with
    | none => exact processReceipt_data_conservation cfg ap decoder st receipt data hwf hr hres hpost hnew hratio hsupported
    | some dataId =>
      exact processReceipt_resume_conservation cfg ap decoder st receipt data dataId hwf hr hres hpost hnew hratio hsupported
  | globalDistribution g => exact processReceipt_distribution_conservation cfg ap decoder st receipt g hr

/-- Data routing and resumption retain account uniqueness under the same
postponed receipt shape invariant used by the financial theorem. -/
theorem processReceipt_data_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.AccountsUnique) (hdata : receipt.receipt = .data data) (hplain : data.resumeDataId = none)
    (hpost : st.PostponedFinancialWellFormed)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata hplain] at hsupported ⊢
  cases hroute : Assoc.lookup st.postponedByData data.dataId with
  | none => exact hwf
  | some id =>
    simp only [hroute] at hsupported ⊢
    cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
    | true =>
      simp only [hpending, ite_true] at hsupported ⊢
      cases hwaiting : Assoc.lookup st.postponed id with
      | none => exact hwf
      | some waiting =>
        simp only [hwaiting] at hsupported ⊢
        obtain ⟨_, action, ha, hshape⟩ := hpost.entries id waiting hwaiting
        exact processReceipt_action_accountsUnique cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action hwf ha hshape hsupported
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact hwf

/-- Resuming a yield keeps accounts unique: the stored receipt runs like any other. -/
theorem processReceipt_resume_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (data : DataReceipt) (dataId : Bytes)
    (hwf : st.AccountsUnique) (hdata : receipt.receipt = .data data) (hres : data.resumeDataId = some dataId)
    (hpost : st.PostponedFinancialWellFormed)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  rw [processReceipt_resume cfg ap decoder st receipt data dataId hdata hres] at hsupported ⊢
  by_cases hmoot : (data.data.isNone &&
      Assoc.lookup st.yieldStatus (receipt.receiverId, dataId) == some YieldStatus.resumeInitiated) = true
  · simp only [hmoot, ite_true]; exact hwf
  · simp only [hmoot, Bool.false_eq_true, ite_false] at hsupported ⊢
    cases hy : Assoc.lookup st.yieldReceipts (receipt.receiverId, dataId) with
    | none => exact hwf
    | some y =>
      simp only [hy] at hsupported ⊢
      obtain ⟨a, ha, hshape⟩ := hpost.yieldEntries _ y hy
      simp only [ha] at hsupported ⊢
      exact runActionReceipt_accountsUnique cfg ap decoder (resumeYieldState st (receipt.receiverId, dataId)) y a
        [data.promiseResult] (hwf.congr rfl rfl) ha hshape hsupported

theorem processReceipt_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.AccountsUnique)
    (hpost : st.PostponedFinancialWellFormed) (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_accountsUnique cfg ap decoder st receipt action hwf hr hshape hsupported
  | data data =>
    cases hres : data.resumeDataId with
    | none => exact processReceipt_data_accountsUnique cfg ap decoder st receipt data hwf hr hres hpost hsupported
    | some dataId => exact processReceipt_resume_accountsUnique cfg ap decoder st receipt data dataId hwf hr hres hpost hsupported
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    exact ChainState.accountsUnique_of_ledger (processDistribution_ledger cfg ap st receipt g) hwf

end Near
