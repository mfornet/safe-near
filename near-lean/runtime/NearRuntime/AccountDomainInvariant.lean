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
    cases hy : action.yieldDataId with
    | some dataId =>
      rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId hr hy]
      split
      · exact hwf
      · exact hwf
    | none =>
      cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
      | false =>
        rw [processReceipt_waiting cfg ap decoder st receipt action hr hy he]
        exact hwf
      | true =>
        rw [processReceipt_ready cfg ap decoder st receipt action hr hy he]
        unfold processedOfExec
        split
        · exact hwf
        · exact applyActionReceipt_accountsUnique_of_systemAbsent
            (readyActionContext cfg ap decoder st receipt action) (consumeReceiptDataState st action) hwf hmissing
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
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
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · exact hwf
      · split
        · rename_i y _
          split
          · rename_i a _
            rw [runActionReceipt_eq]
            unfold processedOfExec
            split
            · exact hwf
            · exact applyActionReceipt_accountsUnique_of_systemAbsent _ _ hwf hmissing
          · exact hwf
        · exact hwf
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    have hl := processDistribution_ledger cfg ap st receipt g
    unfold ChainState.ledgerState at hl
    simp only [Prod.mk.injEq] at hl
    exact hwf.congr hl.1.symm hl.2.1.symm
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
  · intro accounting; exact processReceipt_accountDomainInvariant cfg { ap with storageAccounting := accounting } decoder
  · intro before hb; exact hb
  · intro before receipt hb; exact hb
  · intro before after hb hstep
    refine ⟨hb.1.congr hstep.accounts.symm hstep.accessKeys.symm, ?_⟩
    have h2 := hb.2
    unfold ChainState.SystemAccountAbsent ChainState.account? at h2 ⊢
    rw [hstep.accounts]
    exact h2
  · exact h

end Near
