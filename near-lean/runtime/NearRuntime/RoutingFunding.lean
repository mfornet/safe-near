import NearRuntime.ProcessedFunding

namespace Near
open Wasm.Near

/-- Financially relevant postponed-map structure. This is not full dependency-
graph validity or fairness: ids are unique, match their payloads, and contain
financially scoped action receipts. -/
structure ChainState.PostponedFinancialWellFormed (st : ChainState) : Prop where
  unique : Assoc.KeysUnique st.postponed
  entries : ∀ id receipt, Assoc.lookup st.postponed id = some receipt →
    receipt.receiptId = id ∧ ∃ action, receipt.receipt = .action action ∧ ReceiptFinancialShape receipt

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
    (st : ChainState) (receipt : Receipt) (data : DataReceipt) (hdata : receipt.receipt = .data data) :
    processReceipt cfg ap decoder st receipt =
      match Assoc.lookup st.postponedByData data.dataId with
      | none => { state := { st with receivedData := Assoc.insert st.receivedData data.dataId data.data } }
      | some id =>
        let received := receivePostponedDataState st data
        let pending := (Assoc.lookup st.pendingDataCount id).getD 1 - 1
        if pending == 0 then
          match Assoc.lookup st.postponed id with
          | none => { state := received }
          | some waiting => processReceipt cfg ap decoder (releasePostponedState received id) waiting
        else { state := { received with pendingDataCount := Assoc.insert received.pendingDataCount id pending } } := by
  rw [processReceipt]
  simp only [hdata]
  repeat' (first | rfl | contradiction | split)
  all_goals simp_all [receivePostponedDataState, releasePostponedState]

/-- Incoming data has zero value. Whether it only updates metadata or resumes
an action, the original postponed asset is counted exactly once. -/
theorem processReceipt_data_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.AccountsUnique) (hdata : receipt.receipt = .data data)
    (hpost : st.PostponedFinancialWellFormed) (hnew : cfg.accountCostIncrease = true)
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
        have hf := processReceipt_action_conservation cfg ap decoder
          (releasePostponedState (receivePostponedDataState st data) id) waiting action hwf ha hshape hnew hratio
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
  | action action => exact processReceipt_action_conservation cfg ap decoder st receipt action hwf hr hshape hnew hratio hpost.unique hfresh hsupported
  | data data => exact processReceipt_data_conservation cfg ap decoder st receipt data hwf hr hpost hnew hratio hsupported

/-- Data routing and resumption retain account uniqueness under the same
postponed receipt shape invariant used by the financial theorem. -/
theorem processReceipt_data_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (data : DataReceipt)
    (hwf : st.AccountsUnique) (hdata : receipt.receipt = .data data)
    (hpost : st.PostponedFinancialWellFormed)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  rw [processReceipt_data cfg ap decoder st receipt data hdata] at hsupported ⊢
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

theorem processReceipt_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.AccountsUnique)
    (hpost : st.PostponedFinancialWellFormed) (hshape : ReceiptFinancialShape receipt)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_accountsUnique cfg ap decoder st receipt action hwf hr hshape hsupported
  | data data => exact processReceipt_data_accountsUnique cfg ap decoder st receipt data hwf hr hpost hsupported

end Near
