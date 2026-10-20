import NearRuntime.ReceiptQueueConservation

namespace Near
open Wasm.Near

theorem convertTransaction_accountsUnique (cfg : RuntimeConfig) (ap : ApplyState)
    (before after : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : before.AccountsUnique) (hc : convertTransaction cfg ap before tx = .ok (after, receipt, cost)) :
    after.AccountsUnique := by
  obtain ⟨signer, key, _, _, hcommit, _⟩ := convertTransaction_success_commit cfg ap before after tx receipt cost hc
  let expected := Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions
  have hu : (commitTransaction before tx signer key expected).1.AccountsUnique :=
    h.setAccount tx.signerId { signer with amount := signer.amount - expected.total }
  have he := congrArg (fun result => result.1) hcommit
  dsimp only at he
  rw [← he]
  exact hu

theorem convertTransaction_queue_frame (cfg : RuntimeConfig) (ap : ApplyState)
    (before after : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hc : convertTransaction cfg ap before tx = .ok (after, receipt, cost)) :
    after.postponed = before.postponed ∧ after.delayed = before.delayed := by
  obtain ⟨signer, key, _, _, hcommit, _⟩ := convertTransaction_success_commit cfg ap before after tx receipt cost hc
  have hf := congrArg (fun result => result.1.receiptQueues) hcommit
  exact ⟨(congrArg Prod.fst hf).symm, (congrArg Prod.snd hf).symm⟩

theorem convertTransaction_totalFunds_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (before after : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : before.AccountsUnique) (hsigner : tx.signerId ≠ systemAccount)
    (hc : convertTransaction cfg ap before tx = .ok (after, receipt, cost)) :
    after.totalFunds cfg + Fees.receiptFunds cfg receipt + cost.gasBurnt * ap.gasPrice = before.totalFunds cfg := by
  have hb := convertTransaction_conservation cfg ap before after tx receipt cost h hsigner hc
  have hf := convertTransaction_queue_frame cfg ap before after tx receipt cost hc
  have hq : after.queuedFunds cfg = before.queuedFunds cfg := by
    simp only [ChainState.queuedFunds, ChainState.postponedFunds, hf.1, hf.2]
  dsimp only [ChainState.totalFunds]
  rw [hq]
  omega

theorem convertTransaction_financialShape (cfg : RuntimeConfig) (ap : ApplyState)
    (before after : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hsigner : tx.signerId ≠ systemAccount) (hreceiver : tx.receiverId ≠ systemAccount)
    (hc : convertTransaction cfg ap before tx = .ok (after, receipt, cost)) : ReceiptFinancialShape receipt := by
  obtain ⟨signer, key, _, _, hcommit, _⟩ := convertTransaction_success_commit cfg ap before after tx receipt cost hc
  have he := congrArg (fun result => result.2.1) hcommit
  dsimp only at he
  rw [← he]
  simp [commitTransaction, ReceiptFinancialShape, ActionReceiptFinancialShape, hsigner, hreceiver]

structure TransactionPass.FinancialInvariant (cfg : RuntimeConfig) (initial : ChainState) (pass : TransactionPass) : Prop where
  accounts : pass.1.AccountsUnique
  postponed : pass.1.PostponedFinancialWellFormed
  postponedFrame : pass.1.postponed = initial.postponed
  delayedFrame : pass.1.delayed = initial.delayed
  counter : initial.nextId ≤ pass.1.nextId
  localIds : ReceiptList.FreshIds initial.nextId pass.1.nextId pass.2.2.1
  shapes : ∀ receipt ∈ pass.2.2.1, ReceiptFinancialShape receipt
  ledger : pass.1.totalFunds cfg + receiptsFunds cfg pass.2.2.1 + pass.2.2.2.1 = initial.totalFunds cfg

/-- The actual transaction pass backs its complete local receipt list and
conversion burn, while retaining the structure needed for queue admission.
Actor scope is explicit, matching the existing receipt financial theorem. -/
theorem convertTransactions_financial (cfg : RuntimeConfig) (ap : ApplyState) (initial : ChainState)
    (txs : List Transaction) (haccounts : initial.AccountsUnique) (hpost : initial.PostponedFinancialWellFormed)
    (hactors : ∀ tx ∈ txs, tx.signerId ≠ systemAccount ∧ tx.receiverId ≠ systemAccount) :
    TransactionPass.FinancialInvariant cfg initial (convertTransactions cfg ap initial txs) := by
  unfold convertTransactions
  dsimp only [Id.run, bind, pure]
  apply forIn_id_preserves_mem _ _ _ (TransactionPass.FinancialInvariant cfg initial)
  · exact ⟨haccounts, hpost, rfl, rfl, Nat.le_refl _, ReceiptList.FreshIds.empty _ _,
      by intro receipt hm; contradiction, by simp [receiptsFunds]⟩
  · intro tx hmem pass h
    cases hc : convertTransaction cfg ap pass.1 tx with
    | error error =>
      simp only
      exact ⟨h.accounts, h.postponed, h.postponedFrame, h.delayedFrame, h.counter, h.localIds, h.shapes, h.ledger⟩
    | ok value =>
      obtain ⟨after, receipt, cost⟩ := value
      have ha := hactors tx hmem
      have hframe := convertTransaction_queue_frame cfg ap pass.1 after tx receipt cost hc
      have hcounter := convertTransaction_receipt_counter cfg ap pass.1 after tx receipt cost hc
      have hmono : pass.1.nextId ≤ after.nextId := by omega
      have hsingle : ReceiptList.FreshIds pass.1.nextId after.nextId [receipt] := by
        constructor
        · simp
        · intro candidate hm
          have he := List.mem_singleton.mp hm
          subst candidate
          rw [hcounter.1, hcounter.2]
          exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
      simp only
      refine ⟨convertTransaction_accountsUnique cfg ap pass.1 after tx receipt cost h.accounts hc,
        h.postponed.of_postponed_eq hframe.1, hframe.1.trans h.postponedFrame, hframe.2.trans h.delayedFrame,
        h.counter.trans hmono, ReceiptList.FreshIds.append h.localIds hsingle h.counter hmono, ?_, ?_⟩
      · intro candidate hm
        rcases List.mem_append.mp hm with hold | hnew
        · exact h.shapes candidate hold
        · have he := List.mem_singleton.mp hnew
          subst candidate
          exact convertTransaction_financialShape cfg ap pass.1 after tx receipt cost ha.1 ha.2 hc
      · have hcfs := convertTransaction_totalFunds_conservation cfg ap pass.1 after tx receipt cost h.accounts ha.1 hc
        have hl := h.ledger
        rw [receiptsFunds_append]
        simp only [receiptsFunds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        dsimp only [receiptsFunds] at hl
        omega

end Near
