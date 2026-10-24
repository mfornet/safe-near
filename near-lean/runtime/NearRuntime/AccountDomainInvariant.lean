import NearRuntime.FinancialScope

namespace Near
open Wasm.Near

/-- Account-domain uniqueness does not need financial receipt scope when the
synthetic actor is absent. This includes issue fallback and malformed routing. -/
-- TODO(proof): adapt the cloned proof
theorem processReceipt_accountsUnique_of_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt)
    (hwf : st.AccountsUnique) (hmissing : st.SystemAccountAbsent) :
    (processReceipt cfg ap decoder st receipt).state.AccountsUnique := by
  sorry

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
  · exact h

end Near
