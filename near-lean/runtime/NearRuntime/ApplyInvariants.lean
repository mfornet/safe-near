import NearRuntime.ReservedActorInvariant

namespace Near
open Wasm.Near

/-- Induction over the executor's actual early-exit list loop. -/
theorem forIn_id_preserves {α β : Type} (xs : List α) (initial : β)
    (step : α → β → Id (ForInStep β)) (P : β → Prop) (hinitial : P initial)
    (hstep : ∀ x state, P state →
      match step x state with | .done next | .yield next => P next) :
    P (forIn xs initial step : Id β) := by
  induction xs generalizing initial with
  | nil => exact hinitial
  | cons x xs ih =>
    rw [List.forIn_cons]
    have h := hstep x initial hinitial
    cases he : step x initial with
    | done next => simpa only [he, bind, pure] using h
    | yield next => exact ih next (by simpa only [he, bind, pure] using h)

/-- Exact accumulator types of the two executable early-exit loops. -/
abbrev TransactionLoop := Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) ×
  List Receipt × List Receipt × Nat × Nat

abbrev ReceiptLoop := Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) ×
  List Receipt × List ReceiptIdentityBirth × Nat × Nat × List Receipt × List Receipt × Nat × Bool × Option TrieOverlay.State

/-- State predicates closed under the scheduler updates survive both real loops,
including atomic early exits and final assembly of retained/new delayed work. -/
-- TODO(proof): adapt the cloned proof
theorem applyAttempt_state_predicate (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (P : ChainState → Prop)
    (htx : ∀ before after tx receipt cost, P before →
      convertTransaction cfg ap before tx = .ok (after, receipt, cost) → P after)
    (hreceipt : ∀ accounting before receipt, P before →
      P (processReceipt cfg { ap with storageAccounting := accounting } decoder before receipt).state)
    (hclear : ∀ before, P before → P { before with delayed := [] })
    (hdelay : ∀ before receipt, P before → P { before with delayed := before.delayed ++ [receipt] })
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt) (h : P st) :
    P (applyAttempt cfg ap decoder st txs incoming).state := by
  sorry

/-- An absent synthetic actor stays absent through the actual transaction,
receipt and gas-limit loops, including an early model-issue exit. -/
theorem applyAttempt_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : st.SystemAccountAbsent) :
    (applyAttempt cfg ap decoder st txs incoming).state.SystemAccountAbsent := by
  apply applyAttempt_state_predicate cfg ap decoder ChainState.SystemAccountAbsent
  · exact convertTransaction_systemAbsent cfg ap
  · intro accounting; exact processReceipt_systemAbsent cfg { ap with storageAccounting := accounting } decoder
  · intro before hb; exact hb
  · intro before receipt hb; exact hb
  · exact h

theorem apply_systemAbsent (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (txs : List Transaction)
    (incoming : List Receipt) (h : st.SystemAccountAbsent) :
    (apply cfg ap decoder st txs incoming).state.SystemAccountAbsent := by
  unfold apply
  dsimp only
  split
  · exact h
  · exact applyAttempt_systemAbsent cfg ap decoder st txs incoming h

end Near
