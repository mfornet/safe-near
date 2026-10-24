import NearRuntime.TransactionPassConservation

namespace Near
open Wasm.Near

/-- Structural and protocol scope for the block financial theorem. There is no
financial equation, supplied VM result, or success assumption in this record.
Reserved-target transactions remain outside the existing financial actor scope. -/
structure BlockFinancialPremises (cfg : RuntimeConfig) (st : ChainState)
    (txs : List Transaction) (incoming : List Receipt) : Prop where
  accounts : st.AccountsUnique
  postponed : st.PostponedFinancialWellFormed
  identifiers : st.IdsBelowNext
  incomingIds : ReceiptList.IdsBelow st.nextId incoming
  queueUnique : ((st.delayed ++ incoming).map (·.receiptId)).Nodup
  queueDisjoint : ∀ receipt ∈ st.delayed ++ incoming, Assoc.lookup st.postponed receipt.receiptId = none
  queueShapes : ∀ receipt ∈ st.delayed ++ incoming, ReceiptFinancialShape receipt
  transactionActors : ∀ tx ∈ txs, tx.signerId ≠ systemAccount ∧ tx.receiverId ≠ systemAccount
  accountCostIncrease : cfg.accountCostIncrease = true
  rewardRatio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2

/-- All conversion and receipt costs, rewards and explicit subsidies are
accounted by the actual block attempt, including gas-deferred receipts. -/
theorem applyAttempt_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (h : BlockFinancialPremises cfg st txs incoming)
    (hsupported : (applyAttempt cfg ap decoder st txs incoming).issue = none) :
    let result := applyAttempt cfg ap decoder st txs incoming
    result.state.totalFunds cfg + receiptsFunds cfg result.outgoing + result.tokensBurnt =
      st.totalFunds cfg + receiptsFunds cfg incoming + result.subsidizedAmount := by
  let converted := convertTransactions cfg ap st txs
  let ready : ChainState := { converted.2.1 with delayed := [] }
  let queue := converted.2.2.2.2.1 ++ converted.2.1.delayed ++ incoming
  have hf : TransactionPass.FinancialInvariant cfg st converted :=
    convertTransactions_financial cfg ap st txs h.accounts h.postponed h.transactionActors
  have hqueue : queue = converted.2.2.2.2.1 ++ (st.delayed ++ incoming) := by
    dsimp only [queue]
    rw [hf.delayedFrame, List.append_assoc]
  have hold : ReceiptList.IdsBelow st.nextId (st.delayed ++ incoming) := by
    intro receipt hm id hid
    rcases List.mem_append.mp hm with hd | hi
    · exact ((ChainState.idsBelowNext_iff st).mp h.identifiers).delayed receipt hd id hid
    · exact h.incomingIds receipt hi id hid
  have holdId : ∀ receipt ∈ st.delayed ++ incoming, receipt.receiptId < st.nextId := by
    intro receipt hm
    exact hold receipt hm _ (by simp [Receipt.liveIds])
  have hreadyPost : ready.PostponedFinancialWellFormed :=
    hf.postponed.of_postponed_eq (before := converted.2.1) rfl rfl
  have hadmission : ReceiptQueue.PostponedAdmission ready queue := by
    refine ⟨hreadyPost.idsMatch, ?_, ?_⟩
    · rw [hqueue, List.map_append, List.nodup_append]
      refine ⟨hf.localIds.unique, h.queueUnique, ?_⟩
      intro first hfirst last hlast he
      obtain ⟨minted, hl, hli⟩ := List.mem_map.mp hfirst
      obtain ⟨old, ho, hoi⟩ := List.mem_map.mp hlast
      have hlow := (hf.localIds.bounds minted hl).1
      have hupp := holdId old ho
      rw [hli] at hlow
      rw [hoi, ← he] at hupp
      exact Nat.not_le_of_lt hupp hlow
    · intro receipt hm
      rw [hqueue] at hm
      change Assoc.lookup converted.2.1.postponed receipt.receiptId = none
      rw [hf.postponedFrame]
      rcases List.mem_append.mp hm with hl | ho
      · exact h.identifiers.postponed_lookup_none receipt.receiptId (hf.localIds.bounds receipt hl).1
      · exact h.queueDisjoint receipt ho
  have hshapes : ∀ receipt ∈ queue, ReceiptFinancialShape receipt := by
    intro receipt hm
    rw [hqueue] at hm
    rcases List.mem_append.mp hm with hl | ho
    · exact hf.shapes receipt hl
    · exact h.queueShapes receipt ho
  have hclear : ready.totalFunds cfg + receiptsFunds cfg converted.2.1.delayed = converted.2.1.totalFunds cfg := by
    have h1 : ready.totalBalance = converted.2.1.totalBalance := rfl
    have h2 : ready.postponedFunds cfg = converted.2.1.postponedFunds cfg := rfl
    have h3 : ready.yieldFunds cfg = converted.2.1.yieldFunds cfg := rfl
    have h4 : receiptsFunds cfg ready.delayed = 0 := rfl
    unfold ChainState.totalFunds ChainState.queuedFunds
    omega
  have hbudget : ready.totalFunds cfg + receiptsFunds cfg converted.2.2.2.1 + converted.2.2.2.2.2.1 + receiptsFunds cfg queue =
      st.totalFunds cfg + receiptsFunds cfg incoming := by
    dsimp only [queue]
    rw [receiptsFunds_append, receiptsFunds_append]
    have ht := hf.ledger
    omega
  have hcontinue : converted.1 = none := by
    cases he : converted.1 with
    | none => rfl
    | some result =>
      have hi := hf.returnedIssue result he
      have hs : result.issue = none := by
        simpa only [applyAttempt_eq_stages, show convertTransactions cfg ap st txs = converted from rfl, he] using hsupported
      exact False.elim (hi hs)
  have hstage : applyAttempt cfg ap decoder st txs incoming =
      applyReceiptQueue cfg ap decoder st ready converted.2.2.1 converted.2.2.2.1 0 converted.2.2.2.2.2.1 queue
        converted.2.2.2.2.1.length (converted.2.2.2.2.1.length + converted.2.1.delayed.length) := by
    simpa only [show convertTransactions cfg ap st txs = converted from rfl, hcontinue] using
      applyAttempt_eq_stages cfg ap decoder st txs incoming
  rw [hstage] at hsupported ⊢
  have hc := applyReceiptQueue_conservation cfg ap decoder st ready converted.2.2.1 converted.2.2.2.1 0 converted.2.2.2.2.2.1 queue
    converted.2.2.2.2.1.length (converted.2.2.2.2.1.length + converted.2.1.delayed.length)
    hf.accounts hreadyPost rfl hadmission hshapes h.accountCostIncrease h.rewardRatio hsupported
  rw [hbudget] at hc
  simpa only [Nat.add_zero] using hc

/-- Supported public blocks conserve accounts, delayed/postponed backing,
outgoing receipt backing and net burn, with explicit subsidy as the only source.
The structural/actor scope is exactly `BlockFinancialPremises`. -/
theorem apply_conservation (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (txs : List Transaction) (incoming : List Receipt)
    (h : BlockFinancialPremises cfg st txs incoming)
    (hsupported : (apply cfg ap decoder st txs incoming).issue = none) :
    let result := apply cfg ap decoder st txs incoming
    result.state.totalFunds cfg + receiptsFunds cfg result.outgoing + result.tokensBurnt =
      st.totalFunds cfg + receiptsFunds cfg incoming + result.subsidizedAmount := by
  cases hi : (applyAttempt cfg ap decoder st txs incoming).issue with
  | some issue => simp [apply, hi] at hsupported
  | none =>
    have he : apply cfg ap decoder st txs incoming = applyAttempt cfg ap decoder st txs incoming := by simp [apply, hi]
    rw [he]
    exact applyAttempt_conservation cfg ap decoder st txs incoming h hi

end Near
