import NearRuntime.BlockStatePreservation

namespace Near
open Wasm.Near

/-- Exact transaction-loop accumulator used by the executable block attempt. -/
abbrev TransactionPass := ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat

def convertTransactions (cfg : RuntimeConfig) (ap : ApplyState) (initial : ChainState)
    (txs : List Transaction) : TransactionPass := Id.run do
  let mut st := initial
  let mut outcomes : List (ReceiptId × ExecutionOutcome) := []
  let mut localReceipts : List Receipt := []
  let mut tokensBurnt := 0
  let mut txIndex := 0
  for tx in txs do
    txIndex := txIndex + 1
    match convertTransaction cfg ap st tx with
    | .ok (st', r, cost) =>
      st := st'
      localReceipts := localReceipts ++ [r]
      tokensBurnt := tokensBurnt + cost.gasBurnt * ap.gasPrice
      let o : ExecutionOutcome :=
        { executorId := tx.signerId
          status := .successReceiptId r.receiptId
          receiptIds := [r.receiptId]
          gasBurnt := cost.gasBurnt
          tokensBurnt := cost.gasBurnt * ap.gasPrice }
      outcomes := outcomes ++ [(0, o)]
    | .error e =>
      outcomes := outcomes ++ [(0, { executorId := tx.signerId, status := .failure e })]
  return (st, outcomes, localReceipts, tokensBurnt, txIndex)

/-- Exact receipt-loop stage, including the nested outcome loop, gas deferral
and early issue rollback. This is a proof-facing decomposition, not a replacement
execution semantics: `applyAttempt_eq_stages` connects it definitionally. -/
def applyReceiptQueue (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (initial st : ChainState) (outcomes : List (ReceiptId × ExecutionOutcome))
    (outgoing : List Receipt) (subsidizedAmount tokensBurnt : Nat) (queue : List Receipt) : ApplyResult := Id.run do
  let mut st := st
  let mut outcomes := outcomes
  let mut outgoing := outgoing
  let mut subsidizedAmount := subsidizedAmount
  let mut tokensBurnt := tokensBurnt
  let mut gasUsed := 0
  let mut overLimit := false
  for r in queue do
    if overLimit then
      st := { st with delayed := st.delayed ++ [r] }
    else
      let p := processReceipt cfg ap codeOf st r
      if let some issue := p.issue then
        return { state := initial, outgoing := [], outcomes := [], tokensBurnt := 0, issue := some issue }
      subsidizedAmount := subsidizedAmount + p.subsidizedAmount
      st := p.state
      outgoing := outgoing ++ p.receipts
      outcomes := outcomes ++ p.outcomes
      for (_, o) in p.outcomes do
        gasUsed := gasUsed + o.gasBurnt
        tokensBurnt := tokensBurnt + o.tokensBurnt
      tokensBurnt := tokensBurnt + p.otherTokensBurnt - p.rewards
      if let some limit := ap.gasLimit then
        if gasUsed ≥ limit then overLimit := true
  return { state := st, outgoing, outcomes, tokensBurnt, subsidizedAmount }

/-- Definitional equality with the actual public attempt implementation. -/
theorem applyAttempt_eq_stages (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    applyAttempt cfg ap decoder st txs incoming =
      let converted := convertTransactions cfg ap st txs
      applyReceiptQueue cfg ap decoder st { converted.1 with delayed := [] } converted.2.1 [] 0 converted.2.2.2.1
        (converted.2.2.1 ++ converted.1.delayed ++ incoming) := by
  rfl

/-- Induction over the actual early-exit loop with an invariant indexed by the
unprocessed suffix. It exposes admission facts for the next receipt without
assuming them again after every iteration. -/
theorem forIn_id_suffix_invariant {α β : Type} (items : List α) (initial : β)
    (step : α → β → Id (ForInStep β)) (P : List α → β → Prop) (Q : β → Prop)
    (hinitial : P items initial)
    (hstep : ∀ head rest state, P (head :: rest) state →
      match step head state with | .done next => Q next | .yield next => P rest next)
    (hfinish : ∀ state, P [] state → Q state) : Q (forIn items initial step : Id β) := by
  induction items generalizing initial with
  | nil => exact hfinish initial hinitial
  | cons head rest ih =>
    rw [List.forIn_cons]
    have hp := hstep head rest initial hinitial
    cases he : step head initial with
    | done next => simpa only [he, bind, pure] using hp
    | yield next => exact ih next (by simpa only [he, bind, pure] using hp)

end Near
