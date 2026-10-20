import NearRuntime.FinancialScope

namespace Near
open Wasm.Near

/-- Account-domain uniqueness does not need financial receipt scope when the
synthetic actor is absent. This includes issue fallback and malformed routing. -/
theorem processReceipt_accountsUnique_of_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false =>
      rw [processReceipt_waiting cfg ap decoder st receipt action hr he]
      exact hwf
    | true =>
      rw [processReceipt_ready cfg ap decoder st receipt action hr he]
      unfold processedOfExec
      split
      · exact hwf
      · exact applyActionReceipt_accountsUnique_of_systemAbsent
          (readyActionContext cfg ap decoder st receipt action) (consumeReceiptDataState st action) hwf hmissing
  | data data =>
    rw [processReceipt_data cfg ap decoder st receipt data hr]
    cases hroute : Assoc.lookup st.postponedByData data.dataId with
    | none => exact hwf
    | some id =>
      simp only
      cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
      | false => simp only [Bool.false_eq_true, ite_false]; exact hwf
      | true =>
        simp only [ite_true]
        cases hwaiting : Assoc.lookup st.postponed id with
        | none => exact hwf
        | some waiting =>
          exact processReceipt_accountsUnique_of_systemAbsent cfg ap decoder
            (releasePostponedState (receivePostponedDataState st data) id) waiting hwf hmissing
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

/-- The native account-domain assumptions used by the broader financial scope. -/
def ChainState.AccountDomainInvariant (st : ChainState) : Prop := st.AccountsUnique ∧ st.SystemAccountAbsent

theorem processReceipt_accountDomainInvariant (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (h : st.AccountDomainInvariant) :
    (processReceipt cfg ap decoder st receipt).state.AccountDomainInvariant :=
  ⟨processReceipt_accountsUnique_of_systemAbsent cfg ap decoder st receipt h.1 h.2,
    processReceipt_systemAbsent cfg ap decoder st receipt h.2⟩

/-- Complete blocks retain account uniqueness and reserved-actor absence without
assuming financial scope or success for each receipt. -/
theorem apply_accountDomainInvariant (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (h : st.AccountDomainInvariant) :
    (apply cfg ap decoder st txs incoming).state.AccountDomainInvariant := by
  apply apply_preserves_state cfg ap decoder ChainState.AccountDomainInvariant
  · intro before after tx receipt cost hb hc
    exact ⟨convertTransaction_accountsUnique cfg ap before after tx receipt cost hb.1 hc,
      convertTransaction_systemAbsent cfg ap before after tx receipt cost hb.2 hc⟩
  · exact processReceipt_accountDomainInvariant cfg ap decoder
  · intro before hb; exact hb
  · intro before receipt hb; exact hb
  · exact h

end Near
