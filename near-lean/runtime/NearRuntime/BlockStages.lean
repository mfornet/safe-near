import NearRuntime.BlockStatePreservation

namespace Near
open Wasm.Near

/-- Exact transaction-loop accumulator, including nonlocal output and atomic issues. -/
abbrev TransactionPass := TransactionLoop

def convertTransactions (cfg : RuntimeConfig) (ap : ApplyState) (initial : ChainState)
    (txs : List Transaction) : TransactionPass :=
  Id.run <| forIn txs (none, initial, [], [], [], 0, 0) fun tx pass =>
    match convertTransaction cfg ap pass.2.1 tx with
    | .ok (next, receipt, cost) =>
      let outcome : ExecutionOutcome := {
        executorId := tx.signerId, status := .successReceiptId receipt.receiptId
        receiptIds := [receipt.receiptId], gasBurnt := cost.gasBurnt
        tokensBurnt := cost.gasBurnt * ap.gasPrice }
      if tx.signerId == tx.receiverId then
        .yield (none, next, pass.2.2.1 ++ [(0, outcome)], pass.2.2.2.1,
          pass.2.2.2.2.1 ++ [receipt], pass.2.2.2.2.2.1 + cost.gasBurnt * ap.gasPrice, pass.2.2.2.2.2.2 + 1)
      else
        .yield (none, next, pass.2.2.1 ++ [(0, outcome)], pass.2.2.2.1 ++ [receipt],
          pass.2.2.2.2.1, pass.2.2.2.2.2.1 + cost.gasBurnt * ap.gasPrice, pass.2.2.2.2.2.2 + 1)
    | .error error =>
      match error.issue? with
      | some issue => .done (some { state := initial, outgoing := [], outcomes := [], tokensBurnt := 0, issue := some (0, issue) }, pass.2.1, pass.2.2.1, pass.2.2.2.1, pass.2.2.2.2.1,
          pass.2.2.2.2.2.1, pass.2.2.2.2.2.2 + 1)
      | none => .yield (none, pass.2.1, pass.2.2.1 ++ [(0, { executorId := tx.signerId, status := .failure error })],
          pass.2.2.2.1, pass.2.2.2.2.1, pass.2.2.2.2.2.1, pass.2.2.2.2.2.2 + 1)

/-- Exact receipt-loop stage: transaction gas already counts toward the chunk
limit, old delayed receipts retain FIFO priority, and identity births are retained. -/
def applyReceiptQueue (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (initial st : ChainState) (outcomes : List (ReceiptId × ExecutionOutcome))
    (outgoing : List Receipt) (subsidizedAmount tokensBurnt : Nat) (queue : List Receipt)
    (delayedStart delayedEnd : Nat) : ApplyResult := Id.run do
  let mut st := st
  let mut outcomes := outcomes
  let mut outgoing := outgoing
  let mut identityBirths : List ReceiptIdentityBirth := []
  let mut subsidizedAmount := subsidizedAmount
  let mut tokensBurnt := tokensBurnt
  let mut retainedDelayed : List Receipt := []
  let mut newlyDelayed : List Receipt := []
  let mut gasUsed := outcomes.foldl (fun total pair => total + pair.2.gasBurnt) 0
  let mut overLimit := ap.gasLimit.any (gasUsed ≥ ·)
  let mut storageAccounting := ap.storageAccounting
  for (receipt, position) in queue.zipIdx do
    if overLimit then
      if delayedStart ≤ position && position < delayedEnd then
        retainedDelayed := retainedDelayed ++ [receipt]
      else
        newlyDelayed := newlyDelayed ++ [receipt]
    else
      let processed := processWithInstants cfg { ap with storageAccounting } codeOf st receipt
      storageAccounting := processed.storageAccounting
      if let some issue := processed.issue then
        return { state := initial, outgoing := [], outcomes := [], tokensBurnt := 0, issue := some issue }
      identityBirths := identityBirths ++ processed.identityBirths
      subsidizedAmount := subsidizedAmount + processed.subsidizedAmount
      st := processed.state
      outgoing := outgoing ++ processed.receipts
      outcomes := outcomes ++ processed.outcomes
      for (_, outcome) in processed.outcomes do
        gasUsed := gasUsed + outcome.gasBurnt
        tokensBurnt := tokensBurnt + outcome.tokensBurnt
      gasUsed := gasUsed + processed.extraCompute
      tokensBurnt := tokensBurnt + processed.otherTokensBurnt - processed.rewards
      if let some limit := ap.gasLimit then
        if gasUsed ≥ limit then overLimit := true
  -- Yields that timed out wake up with a resume receipt, after all incoming receipts.
  let (stTimed, timeoutReceipts, timeoutBirths) := resolveYieldTimeouts ap ap.gasLimit gasUsed
    (st.yieldTimeouts.length + 1) (st, [], [])
  st := stTimed
  outgoing := outgoing ++ timeoutReceipts
  identityBirths := identityBirths ++ timeoutBirths
  return {
    state := { st with delayed := retainedDelayed ++ newlyDelayed }, outgoing, outcomes, tokensBurnt, subsidizedAmount, identityBirths
    storageAccounting
    proposals := outcomes.flatMap (·.2.proposals)
    delayedConsumed := initial.delayed.length - retainedDelayed.length, delayedAppended := newlyDelayed.length }

/-- Every public field, including queue metadata and identity births, agrees
with the actual executable attempt. No alternate execution semantics is used. -/
theorem applyAttempt_eq_stages (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) :
    applyAttempt cfg ap decoder st txs incoming =
      let converted := convertTransactions cfg ap st txs
      match converted.1 with
      | some result => result
      | none => applyReceiptQueue cfg ap decoder st { converted.2.1 with delayed := [] } converted.2.2.1
          converted.2.2.2.1 0 converted.2.2.2.2.2.1
          (converted.2.2.2.2.1 ++ converted.2.1.delayed ++ incoming)
          converted.2.2.2.2.1.length (converted.2.2.2.2.1.length + converted.2.1.delayed.length) := by
  unfold applyAttempt
  dsimp only [Id.run, bind, pure]
  generalize ht : (forIn txs _ _ : Id TransactionLoop) = converted
  have heq : converted = convertTransactions cfg ap st txs := by
    rw [← ht]
    unfold convertTransactions
    dsimp only [Id.run]
    congr 1
    funext tx pass
    cases hc : convertTransaction cfg ap pass.2.1 tx with
    | error error =>
      dsimp only
      cases hi : error.issue? <;> rfl
    | ok value =>
      obtain ⟨next, receipt, cost⟩ := value
      split_ifs <;> rfl
  rw [← heq]
  cases converted.1 <;> rfl

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
