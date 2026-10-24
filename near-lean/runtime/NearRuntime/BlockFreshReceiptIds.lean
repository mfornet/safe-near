import NearRuntime.ProcessedFreshReceiptIds

namespace Near
open Wasm.Near

def ApplyResult.FreshReceiptIds (lower : Nat) (result : ApplyResult) : Prop :=
  ReceiptList.FreshIds lower result.state.nextId result.outgoing

structure TransactionLoop.FreshInvariant (lower : Nat) (pass : TransactionLoop) : Prop where
  counter : lower ≤ pass.2.1.nextId
  outgoing : ReceiptList.FreshIds lower pass.2.1.nextId pass.2.2.2.1
  returned : ∀ result, pass.1 = some result → result.FreshReceiptIds lower

structure ReceiptLoop.FreshInvariant (lower : Nat) (pass : ReceiptLoop) : Prop where
  counter : lower ≤ pass.2.1.nextId
  outgoing : ReceiptList.FreshIds lower pass.2.1.nextId pass.2.2.2.1
  returned : ∀ result, pass.1 = some result → result.FreshReceiptIds lower

/-- The actual block accumulator appends disjoint allocation intervals for
nonlocal transactions and executed receipts. Early issues discard output atomically. -/
-- TODO(proof): adapt the cloned proof
theorem applyAttempt_freshIds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    (applyAttempt cfg ap decoder st txs incoming).FreshReceiptIds st.nextId := by
  sorry

/-- A public block's outgoing envelope ids are distinct and allocated no earlier
than the initial counter, on supported and rejected attempts alike. -/
theorem apply_freshIds (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    (apply cfg ap decoder st txs incoming).FreshReceiptIds st.nextId := by
  unfold apply
  dsimp only
  split
  · exact ReceiptList.FreshIds.empty _ _
  · exact applyAttempt_freshIds cfg ap decoder st txs incoming

/-- New outgoing envelopes cannot reuse any reference below the old counter. -/
theorem apply_outgoing_id_ne_old (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (receipt : Receipt) (hm : receipt ∈ (apply cfg ap decoder st txs incoming).outgoing)
    (id : Nat) (hid : id < st.nextId) : receipt.receiptId ≠ id := by
  have hl := ((apply_freshIds cfg ap decoder st txs incoming).bounds receipt hm).1
  intro he
  rw [he] at hl
  exact Nat.not_le_of_lt hid hl

end Near
