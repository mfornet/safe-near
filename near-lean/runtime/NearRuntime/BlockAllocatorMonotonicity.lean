import NearRuntime.AllocatorMonotonicity

namespace Near
open Wasm.Near

/-- Both actual block loops retain all ids allocated before the attempt. Early
model issues return the initial state; gas-limit deferral does not allocate. -/
theorem applyAttempt_nextId_mono (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    st.nextId ≤ (applyAttempt cfg ap decoder st txs incoming).state.nextId := by
  apply applyAttempt_state_predicate cfg ap decoder (fun state => st.nextId ≤ state.nextId)
  · intro before after tx receipt cost hb hc
    have hn := (convertTransaction_receipt_counter cfg ap before after tx receipt cost hc).2
    omega
  · intro accounting before receipt hb
    exact hb.trans (processReceipt_nextId_mono cfg { ap with storageAccounting := accounting } decoder before receipt)
  · intro before hb; exact hb
  · intro before receipt hb; exact hb
  · exact Nat.le_refl _

/-- A public block application never rewinds the initial allocator, including
atomic unsupported/incomplete attempts. -/
theorem apply_nextId_mono (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    st.nextId ≤ (apply cfg ap decoder st txs incoming).state.nextId := by
  unfold apply
  dsimp only
  split
  · exact Nat.le_refl _
  · exact applyAttempt_nextId_mono cfg ap decoder st txs incoming

/-- Previously allocated external references remain bounded after processing a
receipt, even when that processing emits further work. -/
theorem processReceipt_retains_id_bound (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (id : Nat)
    (h : id < st.nextId) : id < (processReceipt cfg ap decoder st receipt).state.nextId :=
  h.trans_le (processReceipt_nextId_mono cfg ap decoder st receipt)

theorem apply_retains_id_bound (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (id : Nat)
    (h : id < st.nextId) : id < (apply cfg ap decoder st txs incoming).state.nextId :=
  h.trans_le (apply_nextId_mono cfg ap decoder st txs incoming)

end Near
