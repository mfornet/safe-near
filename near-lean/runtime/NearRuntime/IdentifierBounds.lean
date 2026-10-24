import NearRuntime.RewardBacking

namespace Near
open Wasm.Near

/-- Receipt identities and dependency references share the model's allocator. -/
def Receipt.liveIds (receipt : Receipt) : List Nat :=
  receipt.receiptId :: match receipt.receipt with
    | .action action => action.inputDataIds ++ action.outputDataReceivers.map (·.dataId)
    | .data data => [data.dataId]
    | .globalDistribution _ => []

/-- Every identifier owned or referenced by routing state, including map keys,
postponed payloads, dependency routes, received data and delayed receipts. External
incoming queues must be bounded separately. This is a bound, not uniqueness. -/
def ChainState.liveIds (st : ChainState) : List Nat :=
  st.postponed.flatMap (fun entry => entry.1 :: entry.2.liveIds) ++
  st.pendingDataCount.map (·.1) ++
  st.postponedByData.flatMap (fun entry => [entry.1, entry.2]) ++
  st.receivedData.map (·.1) ++ st.delayed.flatMap Receipt.liveIds

def ChainState.IdsBelowNext (st : ChainState) : Prop :=
  ∀ id ∈ st.liveIds, id < st.nextId

/-- A frame on routing references and a monotone allocator preserve its bound. -/
theorem ChainState.IdsBelowNext.of_frame {before after : ChainState}
    (h : before.IdsBelowNext) (hids : after.liveIds = before.liveIds)
    (hnext : before.nextId ≤ after.nextId) : after.IdsBelowNext := by
  intro id hmem
  exact (h id (hids ▸ hmem)).trans_le hnext

/-- The next allocated identity cannot coincide with any live routing reference. -/
theorem ChainState.IdsBelowNext.fresh {st : ChainState} (h : st.IdsBelowNext) :
    st.nextId ∉ st.liveIds := by
  intro hmem
  exact Nat.lt_irrefl _ (h _ hmem)

theorem ChainState.IdsBelowNext.freshId {st : ChainState} (h : st.IdsBelowNext) :
    st.freshId.2.IdsBelowNext :=
  h.of_frame rfl (Nat.le_add_right _ _)

/-- Materialization only allocates ids; it cannot change pre-existing routing
references. Its emitted receipts are a separate output of this pass. -/
theorem materializeFunctionCall_idsBelowNext (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) (h : initial.IdsBelowNext) :
    (materializeFunctionCallRaw c isLast outcome initial).state.IdsBelowNext := by
  apply h.of_frame
  · have hf := congrArg ChainState.liveIds (materializeFunctionCallRaw_frame c isLast outcome initial)
    exact hf
  · rw [materializeFunctionCallRaw_nextId]
    omega

/-- Successful transaction conversion preserves every old routing reference. -/
theorem convertTransaction_liveIds (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hc : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) : st'.liveIds = st.liveIds := by
  obtain ⟨signer, key, _, _, hcommit, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost hc
  have hf := congrArg (fun result => result.1.liveIds) hcommit
  exact hf.symm

/-- Conversion advances the allocator and retains the bound for existing work. -/
theorem convertTransaction_idsBelowNext (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : st.IdsBelowNext) (hc : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    st'.IdsBelowNext := by
  apply h.of_frame (convertTransaction_liveIds cfg ap st st' tx receipt cost hc)
  have hn := (convertTransaction_receipt_counter cfg ap st st' tx receipt cost hc).2
  omega

/-- A converted transaction's receipt id is fresh against all routing references,
including postponed keys and delayed dependency references. -/
theorem convertTransaction_receipt_fresh (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : st.IdsBelowNext) (hc : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    receipt.receiptId ∉ st.liveIds := by
  rw [(convertTransaction_receipt_counter cfg ap st st' tx receipt cost hc).1]
  exact h.fresh

/-- Every id allocated for a promise is outside all previously live routing
references, rather than merely distinct from the other newly allocated ids. -/
theorem allocateFunctionCallIds_fresh (specs : List ReceiptSpec) (initial : ChainState)
    (h : initial.IdsBelowNext) (id : ReceiptId)
    (hmem : id ∈ (allocateFunctionCallIds specs initial).2.toList) : id ∉ initial.liveIds := by
  have hb := (allocateFunctionCallIds_bounds specs initial id hmem).1
  intro hold
  have := h id hold
  omega

/-- The bound discharges the postponed-slot freshness premise used by local
conservation, for any id at or beyond the allocator frontier. -/
theorem ChainState.IdsBelowNext.postponed_lookup_none {st : ChainState}
    (h : st.IdsBelowNext) (id : ReceiptId) (hfrontier : st.nextId ≤ id) :
    Assoc.lookup st.postponed id = none := by
  apply Assoc.lookup_none_of_key_not_mem
  intro hmem
  obtain ⟨entry, hentry, he⟩ := List.mem_map.mp hmem
  have hp : id ∈ st.postponed.flatMap (fun entry => entry.1 :: entry.2.liveIds) := by
    apply List.mem_flatMap.mpr
    exact ⟨entry, hentry, by simp [he]⟩
  have hall : id ∈ st.liveIds := by
    simp only [ChainState.liveIds, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
  have := h id hall
  omega

/-- Converted transaction receipts introduce exactly one identity and no data
dependencies. All their identifiers lie below the resulting allocator. -/
theorem convertTransaction_receipt_idsBelowNext (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hc : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    ∀ id ∈ receipt.liveIds, id < st'.nextId := by
  obtain ⟨signer, key, _, _, hcommit, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost hc
  have hf := congrArg (fun result => result.2.1.liveIds) hcommit
  change [st.nextId] = receipt.liveIds at hf
  intro id hmem
  rw [← hf] at hmem
  have hid : id = st.nextId := List.mem_singleton.mp hmem
  have hn := (convertTransaction_receipt_counter cfg ap st st' tx receipt cost hc).2
  omega

/-- A newly converted transaction receipt cannot overwrite an old postponed
slot when later admitted to receipt processing. -/
theorem convertTransaction_postponed_fresh (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : st.IdsBelowNext) (hc : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    Assoc.lookup st'.postponed receipt.receiptId = none := by
  have hf := convertTransaction_liveIds cfg ap st st' tx receipt cost hc
  apply Assoc.lookup_none_of_key_not_mem
  intro hmem
  obtain ⟨entry, hentry, he⟩ := List.mem_map.mp hmem
  have hp : receipt.receiptId ∈ st'.postponed.flatMap (fun entry => entry.1 :: entry.2.liveIds) :=
    List.mem_flatMap.mpr ⟨entry, hentry, by simp [he]⟩
  have hall : receipt.receiptId ∈ st'.liveIds := by
    simp only [ChainState.liveIds, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hp)))
  rw [hf] at hall
  exact convertTransaction_receipt_fresh cfg ap st st' tx receipt cost h hc hall

end Near
