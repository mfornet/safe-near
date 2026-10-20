import NearRuntime.BlockStages

namespace Near
open Wasm.Near

abbrev ReceiptPass := ReceiptLoop

/-- Receipt routing owns postponed state but never changes the persistent delayed
queue; the block loop collects deferrals in separate buffers. -/
theorem processReceipt_delayed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) : (processReceipt cfg ap decoder st receipt).state.delayed = st.delayed := by
  cases hr : receipt.receipt with
  | action action =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false => rw [processReceipt_waiting cfg ap decoder st receipt action hr he]; rfl
    | true => exact congrArg Prod.snd (processReceipt_ready_receiptQueues cfg ap decoder st receipt action hr he)
  | data data =>
    rw [processReceipt_data cfg ap decoder st receipt data hr]
    cases hroute : Assoc.lookup st.postponedByData data.dataId with
    | none => rfl
    | some id =>
      dsimp only
      cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
      | false => simp only [Bool.false_eq_true, ite_false]; rfl
      | true =>
        simp only [ite_true]
        cases hwaiting : Assoc.lookup st.postponed id with
        | none => rfl
        | some waiting =>
          exact processReceipt_delayed cfg ap decoder
            (releasePostponedState (receivePostponedDataState st data) id) waiting
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

def ApplyResult.ReceiptLedger (cfg : RuntimeConfig) (assets initialSubsidy : Nat) (result : ApplyResult) : Prop :=
  result.issue = none → result.state.totalFunds cfg + receiptsFunds cfg result.outgoing + result.tokensBurnt + initialSubsidy =
    assets + result.subsidizedAmount

structure ReceiptQueue.FinancialInvariant (cfg : RuntimeConfig) (assets initialSubsidy : Nat)
    (remaining : List (Receipt × Nat)) (pass : ReceiptPass) : Prop where
  continuing : pass.1 = none
  accounts : pass.2.1.AccountsUnique
  postponed : pass.2.1.PostponedFinancialWellFormed
  delayed : pass.2.1.delayed = []
  admission : ReceiptQueue.PostponedAdmission pass.2.1 (remaining.map Prod.fst)
  shapes : ∀ receipt ∈ remaining.map Prod.fst, ReceiptFinancialShape receipt
  ledger : pass.2.1.totalFunds cfg + receiptsFunds cfg pass.2.2.2.1 + pass.2.2.2.2.2.2.1 +
    receiptsFunds cfg pass.2.2.2.2.2.2.2.1 + receiptsFunds cfg pass.2.2.2.2.2.2.2.2.1 +
    receiptsFunds cfg (remaining.map Prod.fst) + initialSubsidy = assets + pass.2.2.2.2.2.1

def ReceiptQueue.TerminalLedger (cfg : RuntimeConfig) (assets initialSubsidy : Nat) (pass : ReceiptPass) : Prop :=
  match pass.1 with
  | some result => result.ReceiptLedger cfg assets initialSubsidy
  | none => pass.2.1.delayed = [] ∧
      pass.2.1.totalFunds cfg + receiptsFunds cfg pass.2.2.2.1 + pass.2.2.2.2.2.2.1 +
      receiptsFunds cfg pass.2.2.2.2.2.2.2.1 + receiptsFunds cfg pass.2.2.2.2.2.2.2.2.1 + initialSubsidy =
        assets + pass.2.2.2.2.2.1

theorem receiptsFunds_cons (cfg : RuntimeConfig) (receipt : Receipt) (rest : List Receipt) :
    receiptsFunds cfg (receipt :: rest) = Fees.receiptFunds cfg receipt + receiptsFunds cfg rest := rfl

/-- Conservation across the actual indexed receipt loop, including both delayed
buffers, transaction gas, callback resumption, refunds and rewards. The input
state has its delayed queue cleared by the preceding block stage. -/
theorem applyReceiptQueue_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (initial st : ChainState) (outcomes : List (ReceiptId × ExecutionOutcome)) (outgoing : List Receipt)
    (subsidy burnt : Nat) (queue : List Receipt) (delayedStart delayedEnd : Nat) (haccounts : st.AccountsUnique)
    (hpost : st.PostponedFinancialWellFormed) (hdelayed : st.delayed = [])
    (hadmission : ReceiptQueue.PostponedAdmission st queue)
    (hshapes : ∀ receipt ∈ queue, ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    (applyReceiptQueue cfg ap decoder initial st outcomes outgoing subsidy burnt queue delayedStart delayedEnd).ReceiptLedger cfg
      (st.totalFunds cfg + receiptsFunds cfg outgoing + burnt + receiptsFunds cfg queue) subsidy := by
  let assets := st.totalFunds cfg + receiptsFunds cfg outgoing + burnt + receiptsFunds cfg queue
  unfold applyReceiptQueue
  dsimp only [Id.run, bind, pure]
  generalize hloop : (forIn queue.zipIdx _ _ : Id ReceiptPass) = result
  have hfinal : ReceiptQueue.TerminalLedger cfg assets subsidy result := by
    rw [← hloop]
    apply forIn_id_suffix_invariant _ _ _ (ReceiptQueue.FinancialInvariant cfg assets subsidy)
      (ReceiptQueue.TerminalLedger cfg assets subsidy)
    · refine ⟨rfl, haccounts, hpost, hdelayed, ?_, ?_, ?_⟩
      · simpa only [List.zipIdx_map_fst] using hadmission
      · simpa only [List.zipIdx_map_fst] using hshapes
      · simp only [List.zipIdx_map_fst, receiptsFunds, List.map_nil, List.sum_nil, Nat.add_zero]
        rfl
    · intro head rest pass h
      have hn : head.1.receiptId ∉ (rest.map Prod.fst).map (·.receiptId) ∧
          ((rest.map Prod.fst).map (·.receiptId)).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using h.admission.unique
      have hscope : ∀ receipt ∈ rest.map Prod.fst, ReceiptFinancialShape receipt := by
        intro receipt hm; exact h.shapes receipt (by simp [hm])
      by_cases hover : pass.2.2.2.2.2.2.2.2.2.2 = true
      · simp only [hover, ite_true]
        have hadmit : ReceiptQueue.PostponedAdmission pass.2.1 (rest.map Prod.fst) := by
          refine ⟨h.admission.storedIdsMatch, hn.2, ?_⟩
          intro receipt hm
          exact h.admission.disjoint receipt (by simp [hm])
        have hl := h.ledger
        simp only [List.map_cons, receiptsFunds_cons] at hl
        split_ifs
        all_goals
          refine ⟨rfl, h.accounts, h.postponed, h.delayed, hadmit, hscope, ?_⟩
          dsimp only
          rw [receiptsFunds_append]
          simp only [receiptsFunds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          dsimp only [receiptsFunds] at hl
          omega
      · simp only [hover, Bool.false_eq_true, ite_false]
        cases hi : (processReceipt cfg ap decoder pass.2.1 head.1).issue with
        | some issue => simp [ReceiptQueue.TerminalLedger, ApplyResult.ReceiptLedger]
        | none =>
          dsimp only
          have hshape := h.shapes head.1 (by simp)
          have hfresh := h.admission.disjoint head.1 (by simp)
          have hfund := processReceipt_fundingInvariant cfg ap decoder pass.2.1 head.1
            ⟨h.accounts, h.postponed⟩ hshape hi
          have hadmit := h.admission.after_process cfg ap decoder pass.2.1 head.1 (rest.map Prod.fst)
          have hdelay := (processReceipt_delayed cfg ap decoder pass.2.1 head.1).trans h.delayed
          have hc := processReceipt_conservation cfg ap decoder pass.2.1 head.1 h.accounts h.postponed hfresh hshape hnew hratio hi
          have hb := processReceipt_outcomeLoop_burn cfg ap decoder pass.2.1 head.1 pass.2.2.2.2.2.2.1 pass.2.2.2.2.2.2.2.2.2.1
            h.postponed hshape hnew hratio
          dsimp only [pure] at hb
          have hledger : (processReceipt cfg ap decoder pass.2.1 head.1).state.totalFunds cfg +
              receiptsFunds cfg (pass.2.2.2.1 ++ (processReceipt cfg ap decoder pass.2.1 head.1).receipts) +
              ((forIn (processReceipt cfg ap decoder pass.2.1 head.1).outcomes
                (pass.2.2.2.2.2.2.1, pass.2.2.2.2.2.2.2.2.2.1)
                (fun entry ledger => .yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.gasBurnt)) : Id (Nat × Nat)).1 +
                (processReceipt cfg ap decoder pass.2.1 head.1).otherTokensBurnt - (processReceipt cfg ap decoder pass.2.1 head.1).rewards) +
              receiptsFunds cfg pass.2.2.2.2.2.2.2.1 + receiptsFunds cfg pass.2.2.2.2.2.2.2.2.1 +
              receiptsFunds cfg (rest.map Prod.fst) + subsidy = assets +
                (pass.2.2.2.2.2.1 + (processReceipt cfg ap decoder pass.2.1 head.1).subsidizedAmount) := by
            rw [hb, receiptsFunds_append]
            have hl := h.ledger
            simp only [List.map_cons, receiptsFunds_cons] at hl
            dsimp only [Processed.totalFunds] at hc
            omega
          cases hlimit : ap.gasLimit with
          | none => exact ⟨rfl, hfund.1, hfund.2, hdelay, hadmit, hscope, hledger⟩
          | some limit =>
            dsimp only
            split_ifs <;> exact ⟨rfl, hfund.1, hfund.2, hdelay, hadmit, hscope, hledger⟩
    · intro pass h
      unfold ReceiptQueue.TerminalLedger
      rw [h.continuing]
      exact ⟨h.delayed, by simpa only [List.map_nil, receiptsFunds, List.sum_nil, Nat.add_zero] using h.ledger⟩
  cases he : result.1 with
  | some returned => simpa only [ReceiptQueue.TerminalLedger, he] using hfinal
  | none =>
    have hf := hfinal
    simp only [ReceiptQueue.TerminalLedger, he] at hf
    intro hsupported
    dsimp only [assets, ChainState.totalFunds, ChainState.queuedFunds, ChainState.totalBalance, ChainState.postponedFunds] at hf ⊢
    rw [receiptsFunds_append]
    simp only [hf.1, receiptsFunds, List.map_nil, List.sum_nil, Nat.add_zero] at hf
    dsimp only [receiptsFunds] at hf ⊢
    omega

end Near
