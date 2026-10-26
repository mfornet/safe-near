import NearRuntime.ApplyInvariants

namespace Near
open Wasm.Near

/-- Successful ordinary receipt rewards are backed by that receipt's burn,
independently of its account funding equation. -/
theorem applyActionReceipt_success_reward_backed (c : ReceiptCtx) (st : ChainState)
    (hpred : c.receipt.predecessorId ≠ systemAccount)
    (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2)
    (hsuccess : (runReceiptActions c st).2 = none) :
    (applyActionReceipt c st).reward ≤ (applyActionReceipt c st).tokensBurnt := by
  let raw := (runReceiptActions c st).1
  have hfinal : applyActionReceipt c st = (finalizeReceipt c st raw none).commitStorage := by
    simp [applyActionReceipt, Exec.commitStorage, raw, hsuccess]
  have ht := congrArg (fun trace => trace.2.2.2.2.2.1) (finalizeReceipt_success_trace c st raw)
  have hr := finalizeReceipt_success_reward_le c st raw
  have hbound := receiptRewardAmount_le raw c.cfg (successSettlement c st raw).burnPrice
    c.action.gasPrice hnew hratio (runReceiptActions_gas_bounds c st).1
  have hlower := settlement_burn_lower_bound_created c.cfg c.action.gasPrice c.ap.gasPrice
    (Fees.receiptGasBudget c.cfg c.receipt.receiverId c.action.actions) raw.gasUsed raw.gasBurnt
    ((st.account? c.receipt.receiverId).isNone && (raw.state.account? c.receipt.receiverId).isSome) hnew
  change raw.gasBurnt * (successSettlement c st raw).burnPrice ≤ (successSettlement c st raw).tokensBurnt at hlower
  simp only [Exec.finalizationTrace, Receipt.isRefund, beq_eq_false_iff_ne.mpr hpred,
    Bool.false_eq_true, ite_false] at ht
  rw [hfinal]
  exact (hr.trans hbound).trans (by simp only [ht, Exec.commitStorage]; omega)

theorem finalizeReceipt_reward_zero (c : ReceiptCtx) (st : ChainState) (raw : Exec)
    (failed : Option RuntimeError) (hfc : raw.gasBurntForFunctionCall = 0) :
    (finalizeReceipt c st raw failed).reward = 0 := by
  apply Nat.eq_zero_of_le_zero
  cases failed with
  | none => simpa [Exec.receiptRewardAmount, hfc] using finalizeReceipt_success_reward_le c st raw
  | some error => simpa [Exec.receiptRewardAmount, hfc] using finalizeReceipt_failure_reward_le c st raw error

/-- Scoped ordinary receipts and canonical refunds cannot deduct a reward from
burn accumulated by an earlier receipt. This covers contract failures too. -/
theorem applyActionReceipt_reward_backed (c : ReceiptCtx) (st : ChainState)
    (hshape : ActionReceiptFinancialShape c.receipt c.action)
    (hnew : c.cfg.accountCostIncrease = true)
    (hratio : c.cfg.fees.burntGasReward.1 ≤ c.cfg.fees.burntGasReward.2) :
    (applyActionReceipt c st).reward ≤ (applyActionReceipt c st).tokensBurnt := by
  by_cases hp : c.receipt.predecessorId = systemAccount
  · obtain ⟨amount, ha⟩ := (by simpa only [ActionReceiptFinancialShape, hp, ite_true] using hshape :
      ∃ amount, c.action.actions = [.transfer amount])
    have hz := refund_runReceiptActions_functionCallGas_zero c st
      (by simp [ha, Fees.totalPrepaid, Action.attachedGas])
    have hr := finalizeReceipt_reward_zero c st (runReceiptActions c st).1 (runReceiptActions c st).2 hz
    simpa only [applyActionReceipt, Exec.commitStorage, hr] using Nat.zero_le (applyActionReceipt c st).tokensBurnt
  · cases he : (runReceiptActions c st).2 with
    | none => exact applyActionReceipt_success_reward_backed c st hp hnew hratio he
    | some error =>
      have hb := finalizeReceipt_failure_reward_le_burn c st (runReceiptActions c st).1 error
        hnew hratio (runReceiptActions_gas_bounds c st).1
      have ht := finalizeReceipt_failure_tokensBurnt c st (runReceiptActions c st).1 error hp
      simpa only [applyActionReceipt, Exec.commitStorage, he, ht] using hb

/-- Gross receipt burn includes any non-gas deposit destruction. -/
def Processed.grossTokensBurnt (processed : Processed) : Nat :=
  (processed.outcomes.map (fun outcome => outcome.2.tokensBurnt)).sum + processed.otherTokensBurnt

/-- Running a stored receipt backs its reward by its burn, like any ready action receipt. -/
theorem runActionReceipt_reward_backed (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (results : List Wasm.PromiseResult) (ha : receipt.receipt = .action action)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    (runActionReceipt cfg ap decoder st receipt action results).rewards ≤
      (runActionReceipt cfg ap decoder st receipt action results).grossTokensBurnt := by
  rw [runActionReceipt_eq]
  unfold processedOfExec
  split
  · exact Nat.zero_le _
  · have hs : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, ha] using hshape
    have hb := applyActionReceipt_reward_backed
      { cfg, ap, receipt, action, promiseResults := results, codeOf := decoder
        vmYields := yieldsOf st receipt.receiverId } st hs hnew hratio
    simpa only [processedExecOutput, Processed.grossTokensBurnt, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, outcomeOf] using
      hb.trans (Nat.le_add_right _ _)

theorem processReceipt_action_reward_backed (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (action : ActionReceipt)
    (ha : receipt.receipt = .action action) (hshape : ReceiptFinancialShape receipt)
    (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    (processReceipt cfg ap decoder st receipt).rewards ≤
      (processReceipt cfg ap decoder st receipt).grossTokensBurnt := by
  cases hy : action.yieldDataId with
  | some dataId =>
    rw [processReceipt_yield_unfold cfg ap decoder st receipt action dataId ha hy]
    split <;> exact Nat.zero_le _
  | none =>
    cases he : (action.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty with
    | false => rw [processReceipt_waiting cfg ap decoder st receipt action ha hy he]; exact Nat.zero_le _
    | true =>
      rw [processReceipt_ready cfg ap decoder st receipt action ha hy he]
      unfold processedOfExec
      split
      · exact Nat.zero_le _
      · have hs : ActionReceiptFinancialShape receipt action := by simpa only [ReceiptFinancialShape, ha] using hshape
        have hb := applyActionReceipt_reward_backed (readyActionContext cfg ap decoder st receipt action)
          (consumeReceiptDataState st action) hs hnew hratio
        simpa only [processedExecOutput, Processed.grossTokensBurnt, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, outcomeOf] using
          hb.trans (Nat.le_add_right _ _)

/-- Real data delivery either has no reward or resumes a scoped postponed action.
Model-issue fallback has zero public burn and reward as well. -/
theorem processReceipt_reward_backed (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt)
    (hpost : st.PostponedFinancialWellFormed) (hshape : ReceiptFinancialShape receipt)
    (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    (processReceipt cfg ap decoder st receipt).rewards ≤
      (processReceipt cfg ap decoder st receipt).grossTokensBurnt := by
  cases hr : receipt.receipt with
  | action action => exact processReceipt_action_reward_backed cfg ap decoder st receipt action hr hshape hnew hratio
  | data data =>
    cases hres : data.resumeDataId with
    | none =>
      rw [processReceipt_data cfg ap decoder st receipt data hr hres]
      cases hroute : Assoc.lookup st.postponedByData data.dataId with
      | none => exact Nat.zero_le _
      | some id =>
        simp only
        cases hpending : ((Assoc.lookup st.pendingDataCount id).getD 1 - 1 == 0) with
        | false => simp only [Bool.false_eq_true, ite_false]; exact Nat.zero_le _
        | true =>
          simp only [ite_true]
          cases hwaiting : Assoc.lookup st.postponed id with
          | none => exact Nat.zero_le _
          | some waiting =>
            obtain ⟨_, action, ha, hs⟩ := hpost.entries id waiting hwaiting
            exact processReceipt_action_reward_backed cfg ap decoder
              (releasePostponedState (receivePostponedDataState st data) id) waiting action ha hs hnew hratio
    | some dataId =>
      rw [processReceipt_resume cfg ap decoder st receipt data dataId hr hres]
      split
      · exact Nat.zero_le _
      · split
        · rename_i y hy
          split
          · rename_i a ha
            obtain ⟨a', ha', hs⟩ := hpost.yieldEntries _ y hy
            have hsame : a' = a := by
              rw [ha] at ha'
              exact (ReceiptEnum.action.inj ha').symm
            subst hsame
            exact runActionReceipt_reward_backed cfg ap decoder _ y a' _ ha' hs hnew hratio
          · exact Nat.zero_le _
        · exact Nat.zero_le _
  | globalDistribution g =>
    rw [processReceipt_distribution cfg ap decoder st receipt g hr]
    obtain ⟨_, _, hw, _⟩ := processDistribution_outcomes cfg ap st receipt g
    rw [hw]
    exact Nat.zero_le _

/-- A backed reward makes the actual burn update additive in the prior ledger.
Natural subtraction therefore cannot consume tokens charged by earlier work. -/
theorem processReceipt_burn_accumulate (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (prior : Nat)
    (hpost : st.PostponedFinancialWellFormed) (hshape : ReceiptFinancialShape receipt)
    (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    let p := processReceipt cfg ap decoder st receipt
    prior + p.grossTokensBurnt - p.rewards = prior + p.netTokensBurnt := by
  have hb := processReceipt_reward_backed cfg ap decoder st receipt hpost hshape hnew hratio
  dsimp only [Processed.netTokensBurnt, Processed.grossTokensBurnt] at hb ⊢
  omega

/-- The executor's actual inner outcome loop accumulates exactly the sum of
reported gross token burn. Gas accumulation does not affect this projection. -/
theorem forIn_outcomes_tokensBurnt (outcomes : List (ReceiptId × ExecutionOutcome)) (prior gas : Nat) :
    (forIn outcomes (prior, gas) (fun entry ledger =>
      pure (.yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.computeUsage))) : Id (Nat × Nat)).1 =
      prior + (outcomes.map (fun entry => entry.2.tokensBurnt)).sum := by
  induction outcomes generalizing prior gas with
  | nil => simp
  | cons entry rest ih =>
    rw [List.forIn_cons]
    dsimp only [bind, pure]
    have hrest := ih (prior + entry.2.tokensBurnt) (gas + entry.2.computeUsage)
    dsimp only [pure] at hrest
    rw [hrest]
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The nested outcome loop followed by the real reward deduction adds precisely
one receipt's net burn to the incoming ledger. -/
theorem processReceipt_outcomeLoop_burn (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (prior gas : Nat)
    (hpost : st.PostponedFinancialWellFormed) (hshape : ReceiptFinancialShape receipt)
    (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    let p := processReceipt cfg ap decoder st receipt
    (forIn p.outcomes (prior, gas) (fun entry ledger =>
      pure (.yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.computeUsage))) : Id (Nat × Nat)).1 +
        p.otherTokensBurnt - p.rewards = prior + p.netTokensBurnt := by
  dsimp only
  rw [forIn_outcomes_tokensBurnt]
  simpa only [Processed.grossTokensBurnt, Nat.add_assoc] using
    processReceipt_burn_accumulate cfg ap decoder st receipt prior hpost hshape hnew hratio

/-- Complete local ledger conservation with arbitrary previously accumulated
burn. The increment is computed by the same outcome loop as block execution. -/
theorem processReceipt_ledger_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (prior gas : Nat)
    (hwf : st.AccountsUnique) (hpost : st.PostponedFinancialWellFormed)
    (hfresh : Assoc.lookup st.postponed receipt.receiptId = none)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let p := processReceipt cfg ap decoder st receipt
    p.totalFunds cfg +
      ((forIn p.outcomes (prior, gas) (fun entry ledger =>
        pure (.yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.computeUsage))) : Id (Nat × Nat)).1 +
          p.otherTokensBurnt - p.rewards) =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + p.subsidizedAmount + prior := by
  have hc := processReceipt_conservation cfg ap decoder st receipt hwf hpost hfresh hshape hnew hratio hsupported
  dsimp only at hc ⊢
  rw [processReceipt_outcomeLoop_burn cfg ap decoder st receipt prior gas hpost hshape hnew hratio]
  omega

end Near
