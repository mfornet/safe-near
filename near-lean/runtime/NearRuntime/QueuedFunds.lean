import NearRuntime.UnifiedReceiptFunding

namespace Near
open Wasm.Near

/-- Each postponed receipt retains its deposits and purchased gas budget. The
map's indexing metadata is not a second copy of the asset. -/
def ChainState.postponedFunds (cfg : RuntimeConfig) (st : ChainState) : Nat :=
  Assoc.mass (Fees.receiptFunds cfg) st.postponed

def ChainState.queuedFunds (cfg : RuntimeConfig) (st : ChainState) : Nat :=
  st.postponedFunds cfg + receiptsFunds cfg st.delayed

/-- Ledger value inside the runtime state, excluding incoming/outgoing receipts
still held by the caller. This is not merely account liquidity. -/
def ChainState.totalFunds (cfg : RuntimeConfig) (st : ChainState) : Nat :=
  st.totalBalance + st.queuedFunds cfg

/-- The exact state update used by the executable waiting-action branch. -/
def postponeActionState (st : ChainState) (receipt : Receipt) (action : ActionReceipt) : ChainState :=
  let missing := action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)
  { st with
    postponed := Assoc.insert st.postponed receipt.receiptId receipt
    pendingDataCount := Assoc.insert st.pendingDataCount receipt.receiptId missing.length
    postponedByData := missing.foldl (fun map id => Assoc.insert map id receipt.receiptId) st.postponedByData }

/-- Actual receipt processing postpones the complete receipt without executing
it, emitting outcomes, burning funds or manufacturing a replacement receipt. -/
theorem processReceipt_waiting (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action)
    (hmissing : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = false) :
    processReceipt cfg ap decoder st receipt = { state := postponeActionState st receipt action } := by
  rw [processReceipt]
  simp only [haction, hmissing, Bool.false_eq_true, ite_false]
  rfl

/-- Fresh indexing is essential: inserting over an existing receipt id could
otherwise discard that receipt's backing. The premise is identifier freshness,
not an assumed conservation equation. -/
theorem postponeActionState_funds (cfg : RuntimeConfig) (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (hunique : Assoc.KeysUnique st.postponed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none) :
    (postponeActionState st receipt action).totalFunds cfg = st.totalFunds cfg + Fees.receiptFunds cfg receipt := by
  have hm := Assoc.mass_insert_accounting (Fees.receiptFunds cfg) st.postponed receipt.receiptId receipt hunique
  simp only [hfresh, Option.map_none, Option.getD_none, Nat.add_zero] at hm
  unfold ChainState.totalFunds ChainState.queuedFunds ChainState.postponedFunds
  change st.totalBalance + (Assoc.mass (Fees.receiptFunds cfg) (Assoc.insert st.postponed receipt.receiptId receipt) +
    receiptsFunds cfg st.delayed) = _
  omega

/-- The executable waiting branch preserves all account and in-flight value
by moving the incoming receipt into the postponed map exactly once. -/
theorem processReceipt_waiting_funds (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (haction : receipt.receipt = .action action)
    (hmissing : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = false)
    (hunique : Assoc.KeysUnique st.postponed) (hfresh : Assoc.lookup st.postponed receipt.receiptId = none) :
    (processReceipt cfg ap decoder st receipt).state.totalFunds cfg = st.totalFunds cfg + Fees.receiptFunds cfg receipt := by
  rw [processReceipt_waiting cfg ap decoder st receipt action haction hmissing]
  exact postponeActionState_funds cfg st receipt action hunique hfresh

def releasePostponedState (st : ChainState) (id : ReceiptId) : ChainState :=
  { st with postponed := Assoc.erase st.postponed id, pendingDataCount := Assoc.erase st.pendingDataCount id }

/-- Data arrival removes precisely the released receipt's backing from the
queue. Processing must account for that receipt as its new incoming asset. -/
theorem releasePostponedState_funds (cfg : RuntimeConfig) (st : ChainState) (id : ReceiptId) (receipt : Receipt)
    (hunique : Assoc.KeysUnique st.postponed) (hlookup : Assoc.lookup st.postponed id = some receipt) :
    (releasePostponedState st id).totalFunds cfg + Fees.receiptFunds cfg receipt = st.totalFunds cfg := by
  have hm := Assoc.mass_erase_lookup (Fees.receiptFunds cfg) st.postponed id hunique
  simp only [hlookup, Option.map_some, Option.getD_some] at hm
  unfold ChainState.totalFunds ChainState.queuedFunds ChainState.postponedFunds
  change st.totalBalance + (Assoc.mass (Fees.receiptFunds cfg) (Assoc.erase st.postponed id) +
    receiptsFunds cfg st.delayed) + _ = _
  omega

/-- Delaying receipts retains their entire backing, not just attached deposits. -/
theorem ChainState.delayed_append_funds (cfg : RuntimeConfig) (st : ChainState) (receipts : List Receipt) :
    ({ st with delayed := st.delayed ++ receipts } : ChainState).totalFunds cfg =
      st.totalFunds cfg + receiptsFunds cfg receipts := by
  simp [ChainState.totalFunds, ChainState.queuedFunds, ChainState.postponedFunds, ChainState.totalBalance, receiptsFunds_append, Nat.add_assoc]

/-- Removing the next delayed receipt transfers its complete backing to the
execution frontier. No quiescence or fairness claim is made. -/
theorem ChainState.delayed_cons_funds (cfg : RuntimeConfig) (st : ChainState) (receipt : Receipt) (rest : List Receipt)
    (hdelayed : st.delayed = receipt :: rest) :
    ({ st with delayed := rest } : ChainState).totalFunds cfg + Fees.receiptFunds cfg receipt = st.totalFunds cfg := by
  simp only [ChainState.totalFunds, ChainState.queuedFunds, ChainState.postponedFunds, ChainState.totalBalance, hdelayed,
    receiptsFunds, List.map_cons, List.sum_cons]
  omega

end Near
