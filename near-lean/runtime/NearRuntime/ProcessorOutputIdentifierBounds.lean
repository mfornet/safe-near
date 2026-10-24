import NearRuntime.FinalizedOutputIdentifierBounds

namespace Near
open Wasm.Near

/-- All ids carried by publicly emitted work are below the committed counter. -/
def Processed.OutputIdsBelowNext (processed : Processed) : Prop :=
  ∀ receipt ∈ processed.receipts, ∀ id ∈ receipt.liveIds, id < processed.state.nextId

/-- Ready actions, waiting admission, data delivery and recursive resumption all
emit bounded receipt and dependency ids. Issues expose no speculative receipts.
Only input/state identifier bounds are required, not financial scope or success. -/
-- TODO(proof): adapt the cloned proof
theorem processReceipt_outputIds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hstate : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).OutputIdsBelowNext := by
  sorry

/-- One processor transition preserves the state bound and establishes the
bound on its complete public output list. This is not an ownership/uniqueness
invariant and places no liveness requirement on the emitted dependencies. -/
theorem processReceipt_identifier_bounds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hstate : st.IdsBelowNext)
    (hreceipt : ∀ id ∈ receipt.liveIds, id < st.nextId) :
    (processReceipt cfg ap decoder st receipt).state.IdsBelowNext ∧
      (processReceipt cfg ap decoder st receipt).OutputIdsBelowNext :=
  ⟨processReceipt_idsBelowNext cfg ap decoder st receipt hstate hreceipt,
    processReceipt_outputIds cfg ap decoder st receipt hstate hreceipt⟩

end Near
