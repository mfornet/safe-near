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
    cases hy : action.yieldDataId with
    | some dataId =>
      rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId hr hy]
      split <;> rfl
    | none =>
      cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
      | false => rw [processReceipt_waiting cfg ap decoder st receipt action hr hy he]; rfl
      | true => exact congrArg (fun q => q.2.1) (processReceipt_ready_receiptQueues cfg ap decoder st receipt action hr hy he)
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
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
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · rfl
      · split
        · rename_i y _
          split
          · rename_i a _
            exact congrArg (fun q => q.2.1) (runActionReceipt_receiptQueues cfg ap decoder
              (resumeYieldState st (receipt.receiverId, dataId)) y a [data.promiseResult])
          · rfl
        · rfl
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    exact (processDistribution_advance cfg ap st receipt g).2.2.2.2.1
termination_by st.postponed.length
decreasing_by exact Assoc.erase_length_lt_of_lookup _ _ _ hwaiting

theorem processWithInstants_delayed (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) :
    (processWithInstants cfg ap decoder st receipt).state.delayed = st.delayed :=
  processWithInstants_state_predicate cfg ap decoder (fun s => s.delayed = st.delayed)
    (fun accounting before receipt hb =>
      (processReceipt_delayed cfg { ap with storageAccounting := accounting } decoder before receipt).trans hb)
    st receipt rfl

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

theorem resolveYieldTimeouts_funds (cfg : RuntimeConfig) (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) :
    ∀ (acc : ChainState × List Receipt × List ReceiptIdentityBirth),
      (resolveYieldTimeouts ap limit used fuel acc).1.totalFunds cfg = acc.1.totalFunds cfg ∧
      receiptsFunds cfg (resolveYieldTimeouts ap limit used fuel acc).2.1 = receiptsFunds cfg acc.2.1 := by
  induction fuel with
  | zero => intro acc; exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    rintro ⟨st, receipts, births⟩
    unfold resolveYieldTimeouts
    dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · split
      · split
        · exact ⟨rfl, rfl⟩
        · split
          · exact ⟨rfl, rfl⟩
          · split
            · refine ⟨(ih _).1.trans rfl, (ih _).2.trans ?_⟩
              simp [receiptsFunds, Fees.receiptFunds]
            · exact ih _
      · exact ⟨rfl, rfl⟩
theorem resolveYieldTimeouts_delayed (ap : ApplyState) (limit : Option Nat) (used fuel : Nat) :
    ∀ (acc : ChainState × List Receipt × List ReceiptIdentityBirth),
      (resolveYieldTimeouts ap limit used fuel acc).1.delayed = acc.1.delayed := by
  induction fuel with
  | zero => intro acc; rfl
  | succ fuel ih =>
    rintro ⟨st, receipts, births⟩
    unfold resolveYieldTimeouts
    dsimp only
    split
    · rfl
    · split
      · split
        · rfl
        · split
          · rfl
          · split
            · exact (ih _).trans rfl
            · exact ih _
      · rfl

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
      by_cases hover : pass.2.2.2.2.2.2.2.2.2.2.1 = true
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
        cases hi : (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).issue with
        | some issue => simp [ReceiptQueue.TerminalLedger, ApplyResult.ReceiptLedger]
        | none =>
          dsimp only
          have hshape := h.shapes head.1 (by simp)
          have hfresh := h.admission.disjoint head.1 (by simp)
          have hfund := processWithInstants_funding cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1 h.accounts h.postponed hfresh
            hshape hnew hratio hi
          have hadmit := h.admission.after_processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1 (rest.map Prod.fst)
          have hdelay := (processWithInstants_delayed cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).trans h.delayed
          have hc := hfund.2.2.2
          have hb := processWithInstants_outcomeLoop_burn cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1 pass.2.2.2.2.2.2.1 pass.2.2.2.2.2.2.2.2.2.1
            hfund.2.2.1
          dsimp only [pure] at hb
          have hledger : (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).state.totalFunds cfg +
              receiptsFunds cfg (pass.2.2.2.1 ++ (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).receipts) +
              ((forIn (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).outcomes
                (pass.2.2.2.2.2.2.1, pass.2.2.2.2.2.2.2.2.2.1)
                (fun entry ledger => .yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.computeUsage)) : Id (Nat × Nat)).1 +
                (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).otherTokensBurnt - (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).rewards) +
              receiptsFunds cfg pass.2.2.2.2.2.2.2.1 + receiptsFunds cfg pass.2.2.2.2.2.2.2.2.1 +
              receiptsFunds cfg (rest.map Prod.fst) + subsidy = assets +
                (pass.2.2.2.2.2.1 + (processWithInstants cfg { ap with storageAccounting := pass.2.2.2.2.2.2.2.2.2.2.2 } decoder pass.2.1 head.1).subsidizedAmount) := by
            rw [hb, receiptsFunds_append]
            have hl := h.ledger
            simp only [List.map_cons, receiptsFunds_cons] at hl
            dsimp only [Processed.totalFunds] at hc
            omega
          cases hlimit : ap.gasLimit with
          | none =>
            simp only [hlimit] at hfund hdelay hadmit hledger
            exact ⟨rfl, hfund.1, hfund.2.1, hdelay, hadmit, hscope, hledger⟩
          | some limit =>
            simp only [hlimit] at hfund hdelay hadmit hledger
            dsimp only
            split_ifs <;> exact ⟨rfl, hfund.1, hfund.2.1, hdelay, hadmit, hscope, hledger⟩
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
    have htf := (resolveYieldTimeouts_funds cfg ap ap.gasLimit result.2.2.2.2.2.2.2.2.2.1
      (result.2.1.yieldTimeouts.length + 1) (result.2.1, [], [])).1
    have hrf := (resolveYieldTimeouts_funds cfg ap ap.gasLimit result.2.2.2.2.2.2.2.2.2.1
      (result.2.1.yieldTimeouts.length + 1) (result.2.1, [], [])).2
    have hdl := resolveYieldTimeouts_delayed ap ap.gasLimit result.2.2.2.2.2.2.2.2.2.1
      (result.2.1.yieldTimeouts.length + 1) (result.2.1, [], [])
    have h0 : receiptsFunds cfg ([] : List Receipt) = 0 := rfl
    dsimp only at hrf
    rw [h0] at hrf
    dsimp only at hdl htf
    have hset : ∀ (S : ChainState) (d : List Receipt),
        ({ S with delayed := d } : ChainState).totalFunds cfg + receiptsFunds cfg S.delayed =
          S.totalFunds cfg + receiptsFunds cfg d := by
      intro S d
      have h1 : ({ S with delayed := d } : ChainState).gasKeyFunds = S.gasKeyFunds := rfl
      have h2 : ChainState.yieldFunds cfg ({ S with delayed := d } : ChainState) = ChainState.yieldFunds cfg S := rfl
      simp only [ChainState.totalFunds, ChainState.queuedFunds, ChainState.totalBalance, ChainState.postponedFunds,
        h1, h2]
      omega
    have hs := hset (resolveYieldTimeouts ap ap.gasLimit result.2.2.2.2.2.2.2.2.2.1
      (result.2.1.yieldTimeouts.length + 1) (result.2.1, [], [])).1
      (result.2.2.2.2.2.2.2.1 ++ result.2.2.2.2.2.2.2.2.1)
    rw [hdl, hf.1, h0, receiptsFunds_append] at hs
    dsimp only [assets]
    rw [receiptsFunds_append]
    have hf2 := hf.2
    dsimp only [assets] at hf2
    rw [hrf]
    omega

end Near
