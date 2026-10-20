import NearRuntime.BlockStages

namespace Near
open Wasm.Near

abbrev ReceiptPass := Option ApplyResult × ChainState × List (ReceiptId × ExecutionOutcome) × List Receipt × Nat × Nat × Nat × Bool

def ApplyResult.ReceiptLedger (cfg : RuntimeConfig) (assets initialSubsidy : Nat) (result : ApplyResult) : Prop :=
  result.issue = none → result.state.totalFunds cfg + receiptsFunds cfg result.outgoing + result.tokensBurnt + initialSubsidy =
    assets + result.subsidizedAmount

structure ReceiptQueue.FinancialInvariant (cfg : RuntimeConfig) (assets initialSubsidy : Nat)
    (remaining : List Receipt) (pass : ReceiptPass) : Prop where
  continuing : pass.1 = none
  accounts : pass.2.1.AccountsUnique
  postponed : pass.2.1.PostponedFinancialWellFormed
  admission : ReceiptQueue.PostponedAdmission pass.2.1 remaining
  shapes : ∀ receipt ∈ remaining, ReceiptFinancialShape receipt
  ledger : pass.2.1.totalFunds cfg + receiptsFunds cfg pass.2.2.2.1 + pass.2.2.2.2.2.1 +
    receiptsFunds cfg remaining + initialSubsidy = assets + pass.2.2.2.2.1

def ReceiptQueue.TerminalLedger (cfg : RuntimeConfig) (assets initialSubsidy : Nat) (pass : ReceiptPass) : Prop :=
  match pass.1 with
  | some result => result.ReceiptLedger cfg assets initialSubsidy
  | none => pass.2.1.totalFunds cfg + receiptsFunds cfg pass.2.2.2.1 + pass.2.2.2.2.2.1 + initialSubsidy =
      assets + pass.2.2.2.2.1

theorem receiptsFunds_cons (cfg : RuntimeConfig) (receipt : Receipt) (rest : List Receipt) :
    receiptsFunds cfg (receipt :: rest) = Fees.receiptFunds cfg receipt + receiptsFunds cfg rest := rfl

/-- Conservation across the actual receipt loop, including gas deferral, nested
outcome accumulation, callback resumption, refunds and rewards. Every admission
premise is propagated from the remaining queue; no financial equation is assumed.
An issue exposes no committed ledger and is excluded by `ReceiptLedger`. -/
theorem applyReceiptQueue_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (initial st : ChainState) (outcomes : List (ReceiptId × ExecutionOutcome)) (outgoing : List Receipt)
    (subsidy burnt : Nat) (queue : List Receipt) (haccounts : st.AccountsUnique)
    (hpost : st.PostponedFinancialWellFormed) (hadmission : ReceiptQueue.PostponedAdmission st queue)
    (hshapes : ∀ receipt ∈ queue, ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    (applyReceiptQueue cfg ap decoder initial st outcomes outgoing subsidy burnt queue).ReceiptLedger cfg
      (st.totalFunds cfg + receiptsFunds cfg outgoing + burnt + receiptsFunds cfg queue) subsidy := by
  let assets := st.totalFunds cfg + receiptsFunds cfg outgoing + burnt + receiptsFunds cfg queue
  unfold applyReceiptQueue
  dsimp only [Id.run, bind, pure]
  generalize hloop : (forIn queue _ _ : Id ReceiptPass) = result
  have hfinal : ReceiptQueue.TerminalLedger cfg assets subsidy result := by
    rw [← hloop]
    apply forIn_id_suffix_invariant _ _ _ (ReceiptQueue.FinancialInvariant cfg assets subsidy)
      (ReceiptQueue.TerminalLedger cfg assets subsidy)
    · exact ⟨rfl, haccounts, hpost, hadmission, hshapes, rfl⟩
    · intro head rest pass h
      by_cases hover : pass.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        have hn : head.receiptId ∉ rest.map (·.receiptId) ∧ (rest.map (·.receiptId)).Nodup := by
          simpa only [List.map_cons, List.nodup_cons] using h.admission.unique
        refine ⟨rfl, h.accounts, h.postponed.of_postponed_eq (before := pass.2.1) rfl, ?_, ?_, ?_⟩
        · refine ⟨h.admission.storedIdsMatch, hn.2, ?_⟩
          intro receipt hm
          exact h.admission.disjoint receipt (by simp [hm])
        · intro receipt hm
          exact h.shapes receipt (by simp [hm])
        · have hf := ChainState.delayed_append_funds cfg pass.2.1 [head]
          have hl := h.ledger
          simp only [receiptsFunds_cons] at hl
          simp only [receiptsFunds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hf
          change ({ pass.2.1 with delayed := pass.2.1.delayed ++ [head] } : ChainState).totalFunds cfg +
            receiptsFunds cfg pass.2.2.2.1 + pass.2.2.2.2.2.1 + receiptsFunds cfg rest + subsidy =
              assets + pass.2.2.2.2.1
          rw [hf]
          omega
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder pass.2.1 head).issue with
        | some issue => simp [ReceiptQueue.TerminalLedger, ApplyResult.ReceiptLedger]
        | none =>
          simp only
          have hshape := h.shapes head (by simp)
          have hfresh := h.admission.disjoint head (by simp)
          have hfund := processReceipt_fundingInvariant cfg ap decoder pass.2.1 head
            ⟨h.accounts, h.postponed⟩ hshape hi
          have hadmit := h.admission.after_process cfg ap decoder pass.2.1 head rest
          have hscope : ∀ receipt ∈ rest, ReceiptFinancialShape receipt := by
            intro receipt hm; exact h.shapes receipt (by simp [hm])
          have hc := processReceipt_conservation cfg ap decoder pass.2.1 head h.accounts h.postponed hfresh hshape hnew hratio hi
          have hb := processReceipt_outcomeLoop_burn cfg ap decoder pass.2.1 head pass.2.2.2.2.2.1 pass.2.2.2.2.2.2.1
            h.postponed hshape hnew hratio
          dsimp only [pure] at hb
          have hledger : (processReceipt cfg ap decoder pass.2.1 head).state.totalFunds cfg +
              receiptsFunds cfg (pass.2.2.2.1 ++ (processReceipt cfg ap decoder pass.2.1 head).receipts) +
              ((forIn (processReceipt cfg ap decoder pass.2.1 head).outcomes (pass.2.2.2.2.2.1, pass.2.2.2.2.2.2.1)
                (fun entry ledger => .yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.gasBurnt)) : Id (Nat × Nat)).1 +
                (processReceipt cfg ap decoder pass.2.1 head).otherTokensBurnt - (processReceipt cfg ap decoder pass.2.1 head).rewards) +
              receiptsFunds cfg rest + subsidy = assets +
                (pass.2.2.2.2.1 + (processReceipt cfg ap decoder pass.2.1 head).subsidizedAmount) := by
            rw [hb, receiptsFunds_append]
            have hl := h.ledger
            simp only [receiptsFunds_cons] at hl
            dsimp only [Processed.totalFunds] at hc
            omega
          cases hlimit : ap.gasLimit with
          | none => exact ⟨rfl, hfund.1, hfund.2, hadmit, hscope, hledger⟩
          | some limit =>
            simp only
            split_ifs <;> exact ⟨rfl, hfund.1, hfund.2, hadmit, hscope, hledger⟩
    · intro pass h
      unfold ReceiptQueue.TerminalLedger
      rw [h.continuing]
      simpa only [receiptsFunds, List.map_nil, List.sum_nil, Nat.add_zero] using h.ledger
  cases he : result.1 with
  | some returned => simpa only [ReceiptQueue.TerminalLedger, he] using hfinal
  | none =>
    intro hsupported
    simpa only [ReceiptQueue.TerminalLedger, he] using hfinal

end Near
