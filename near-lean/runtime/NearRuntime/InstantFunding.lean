import NearRuntime.RewardBacking

namespace Near
open Wasm.Near

theorem receiptsFunds_cons (cfg : RuntimeConfig) (x : Receipt) (xs : List Receipt) :
    receiptsFunds cfg (x :: xs) = Fees.receiptFunds cfg x + receiptsFunds cfg xs := by
  simp [receiptsFunds]

theorem receiptsFunds_filter_split (cfg : RuntimeConfig) (p : Receipt → Bool) (xs : List Receipt) :
    receiptsFunds cfg (xs.filter p) + receiptsFunds cfg (xs.filter fun x => !p x) = receiptsFunds cfg xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, Bool.not_true, ite_true, Bool.false_eq_true, ite_false, receiptsFunds_cons]
      omega
    · have hx' : p x = false := by simpa using hx
      simp only [List.filter_cons, hx', Bool.not_false, ite_true, Bool.false_eq_true, ite_false, receiptsFunds_cons]
      omega

theorem Receipt.fundedShape_shape {r : Receipt} (h : r.fundedShape = true) : ReceiptFinancialShape r := by
  unfold Receipt.fundedShape at h
  unfold ReceiptFinancialShape
  cases hr : r.receipt with
  | action a =>
    simp only [hr] at h
    unfold ActionReceiptFinancialShape
    by_cases hp : r.predecessorId = systemAccount
    · simp only [hp, beq_self_eq_true, ite_true] at h ⊢
      split at h
      · rename_i amount hact
        exact ⟨amount, hact⟩
      · cases h
    · have hp' : (r.predecessorId == systemAccount) = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ite_false, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      simp only [hp, ite_false]
      exact h
  | data _ => trivial
  | globalDistribution _ => trivial

theorem Receipt.isInstant_action {r : Receipt} (h : r.isInstant = true) :
    ∃ a, r.receipt = .action a ∧ (a.yieldDataId.isSome = true ∨ a.inputDataIds = []) := by
  unfold Receipt.isInstant at h
  cases hr : r.receipt with
  | action a =>
    simp only [hr, Bool.or_eq_true, Bool.and_eq_true] at h
    refine ⟨a, rfl, ?_⟩
    rcases h with h | ⟨h, _⟩
    · exact Or.inl h
    · right; simpa using h
  | data _ => simp [hr] at h
  | globalDistribution _ => simp [hr] at h

/-- Instant receipts never wait for data, so the fresh-slot premise of the processor is moot. -/
theorem processReceipt_instant_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt)
    (hwf : st.AccountsUnique) (hpost : st.PostponedFinancialWellFormed) (hinst : receipt.isInstant = true)
    (hshape : ReceiptFinancialShape receipt) (hnew : cfg.accountCostIncrease = true)
    (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processReceipt cfg ap decoder st receipt).issue = none) :
    let processed := processReceipt cfg ap decoder st receipt
    processed.totalFunds cfg + processed.netTokensBurnt =
      st.totalFunds cfg + Fees.receiptFunds cfg receipt + processed.subsidizedAmount := by
  obtain ⟨a, hr, hcase⟩ := Receipt.isInstant_action hinst
  cases hy : a.yieldDataId with
  | some dataId =>
    exact processReceipt_yield_conservation cfg ap decoder st receipt a dataId hr hy hpost.yieldUnique hsupported
  | none =>
    have hempty : a.inputDataIds = [] := by
      rcases hcase with h | h
      · simp [hy] at h
      · exact h
    have hready : (a.inputDataIds.filter fun id => !(Assoc.contains st.receivedData id)).isEmpty = true := by
      simp [hempty]
    exact processReceipt_ready_conservation cfg ap decoder st receipt a hwf hr hy hready hshape hnew hratio hsupported

/-- What holds along the instant receipts a receipt created: state invariants, and the ledger with
the pending instants counted at their full backing. -/
structure InstantLedger (cfg : RuntimeConfig) (base : Nat) (acc : Processed) (pending : List Receipt) : Prop where
  accounts : acc.state.AccountsUnique
  postponed : acc.state.PostponedFinancialWellFormed
  instant : ∀ x ∈ pending, x.isInstant = true
  rewards : acc.rewards ≤ acc.grossTokensBurnt
  ledger : acc.totalFunds cfg + receiptsFunds cfg pending + (acc.grossTokensBurnt - acc.rewards) =
    base + acc.subsidizedAmount

theorem Processed.grossTokensBurnt_append (acc p : Processed) :
    (acc.append p).grossTokensBurnt = acc.grossTokensBurnt + p.grossTokensBurnt := by
  simp only [Processed.grossTokensBurnt, Processed.append, List.map_append, List.sum_append]
  omega

theorem Processed.append_state (acc p : Processed) : (acc.append p).state = p.state := rfl
theorem Processed.append_rewards (acc p : Processed) : (acc.append p).rewards = acc.rewards + p.rewards := rfl
theorem Processed.append_subsidized (acc p : Processed) :
    (acc.append p).subsidizedAmount = acc.subsidizedAmount + p.subsidizedAmount := rfl
theorem Processed.append_receipts (acc p : Processed) : (acc.append p).receipts = acc.receipts ++ p.receipts := rfl

theorem instantAccumulate_gross (acc p : Processed) :
    (instantAccumulate acc p).grossTokensBurnt = acc.grossTokensBurnt + p.grossTokensBurnt := by
  unfold instantAccumulate; rw [Processed.grossTokensBurnt_append]; rfl

theorem instantAccumulate_rewards (acc p : Processed) :
    (instantAccumulate acc p).rewards = acc.rewards + p.rewards := rfl

theorem instantAccumulate_subsidized (acc p : Processed) :
    (instantAccumulate acc p).subsidizedAmount = acc.subsidizedAmount + p.subsidizedAmount := rfl

theorem InstantLedger.step (cfg : RuntimeConfig) (ap : ApplyState) (codeOf : Bytes → ContractCode)
    (base : Nat) (acc : Processed) (r : Receipt) (rest : List Receipt)
    (h : InstantLedger cfg base acc (r :: rest)) (hs : r.fundedShape = true)
    (hi : (instantStep cfg ap codeOf acc r).issue = none)
    (hnew : cfg.accountCostIncrease = true) (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2) :
    InstantLedger cfg base (instantAccumulate acc (instantStep cfg ap codeOf acc r))
      (rest ++ (instantStep cfg ap codeOf acc r).receipts.filter Receipt.isInstant) := by
  have hshape := Receipt.fundedShape_shape hs
  have hinst : r.isInstant = true := h.instant r (by simp)
  have hacc := processReceipt_accountsUnique cfg { ap with storageAccounting := acc.storageAccounting } codeOf
    acc.state r h.accounts h.postponed hshape hi
  have hpost := processReceipt_postponedWellFormed cfg { ap with storageAccounting := acc.storageAccounting } codeOf
    acc.state r h.postponed hshape
  have hc := processReceipt_instant_conservation cfg { ap with storageAccounting := acc.storageAccounting } codeOf
    acc.state r h.accounts h.postponed hinst hshape hnew hratio hi
  have hp := processReceipt_reward_backed cfg { ap with storageAccounting := acc.storageAccounting } codeOf
    acc.state r h.postponed hshape hnew hratio
  change (instantStep cfg ap codeOf acc r).totalFunds cfg + (instantStep cfg ap codeOf acc r).netTokensBurnt =
    acc.state.totalFunds cfg + Fees.receiptFunds cfg r + (instantStep cfg ap codeOf acc r).subsidizedAmount at hc
  change (instantStep cfg ap codeOf acc r).rewards ≤ (instantStep cfg ap codeOf acc r).grossTokensBurnt at hp
  have hsplit := receiptsFunds_filter_split cfg Receipt.isInstant (instantStep cfg ap codeOf acc r).receipts
  have hl := h.ledger
  simp only [receiptsFunds_cons] at hl
  have hnet : (instantStep cfg ap codeOf acc r).netTokensBurnt =
      (instantStep cfg ap codeOf acc r).grossTokensBurnt - (instantStep cfg ap codeOf acc r).rewards := rfl
  refine ⟨hacc, hpost, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h.instant x (List.mem_cons_of_mem _ hx)
    · exact (List.mem_filter.mp hx).2
  · have hr := h.rewards
    rw [instantAccumulate_gross, instantAccumulate_rewards]
    omega
  · have hr := h.rewards
    have hacc' : (instantAccumulate acc (instantStep cfg ap codeOf acc r)).totalFunds cfg =
        (instantStep cfg ap codeOf acc r).state.totalFunds cfg +
          (receiptsFunds cfg acc.receipts + receiptsFunds cfg
            ((instantStep cfg ap codeOf acc r).receipts.filter fun x => !x.isInstant)) := by
      simp only [instantAccumulate, Processed.totalFunds, Processed.append_state, Processed.append_receipts,
        receiptsFunds_append]
    have hold : acc.totalFunds cfg = acc.state.totalFunds cfg + receiptsFunds cfg acc.receipts := rfl
    have hP : (instantStep cfg ap codeOf acc r).totalFunds cfg =
        (instantStep cfg ap codeOf acc r).state.totalFunds cfg +
          receiptsFunds cfg (instantStep cfg ap codeOf acc r).receipts := rfl
    rw [hacc', receiptsFunds_append, instantAccumulate_gross, instantAccumulate_rewards,
      instantAccumulate_subsidized]
    omega

/-- A receipt together with the instant receipts it creates conserves funds like a single receipt
and keeps the state invariants. -/
theorem processWithInstants_funding (cfg : RuntimeConfig) (ap : ApplyState) (decoder : Bytes → ContractCode)
    (st : ChainState) (receipt : Receipt) (hwf : st.AccountsUnique) (hpost : st.PostponedFinancialWellFormed)
    (hfresh : Assoc.lookup st.postponed receipt.receiptId = none) (hshape : ReceiptFinancialShape receipt)
    (hnew : cfg.accountCostIncrease = true) (hratio : cfg.fees.burntGasReward.1 ≤ cfg.fees.burntGasReward.2)
    (hsupported : (processWithInstants cfg ap decoder st receipt).issue = none) :
    let p := processWithInstants cfg ap decoder st receipt
    p.state.AccountsUnique ∧ p.state.PostponedFinancialWellFormed ∧ p.rewards ≤ p.grossTokensBurnt ∧
      p.totalFunds cfg + p.netTokensBurnt = st.totalFunds cfg + Fees.receiptFunds cfg receipt + p.subsidizedAmount := by
  let base := st.totalFunds cfg + Fees.receiptFunds cfg receipt
  have key := processWithInstants_induction cfg ap decoder
    (fun acc pending => InstantLedger cfg base acc pending)
    (fun p => p.issue = none → p.state.AccountsUnique ∧ p.state.PostponedFinancialWellFormed ∧
      p.rewards ≤ p.grossTokensBurnt ∧ p.totalFunds cfg + p.netTokensBurnt = base + p.subsidizedAmount)
    (fun st' r' => st' = st ∧ r' = receipt)
    (by
      intro acc h _
      refine ⟨h.accounts, h.postponed, h.rewards, ?_⟩
      have hl := h.ledger
      simp only [receiptsFunds, List.map_nil, List.sum_nil, Nat.add_zero] at hl
      have hr := h.rewards
      change acc.state.totalFunds cfg + receiptsFunds cfg acc.receipts + (acc.grossTokensBurnt - acc.rewards) = _
      change acc.state.totalFunds cfg + receiptsFunds cfg acc.receipts + (acc.grossTokensBurnt - acc.rewards) +
        0 = _ at hl
      omega)
    (by
      intro acc pending issue hsome _ hi
      have hn : issue = none := hi
      simp [hn] at hsome)
    (by
      intro acc r' rest h hs hi
      exact InstantLedger.step cfg ap decoder base acc r' rest h hs hi hnew hratio)
    (by
      intro st' r' hstart hne hi
      exact absurd hi hne)
    (by
      rintro st' r' ⟨h1, h2⟩ hi
      subst st' r'
      have hacc := processReceipt_accountsUnique cfg ap decoder st receipt hwf hpost hshape hi
      have hpost' := processReceipt_postponedWellFormed cfg ap decoder st receipt hpost hshape
      have hc := processReceipt_conservation cfg ap decoder st receipt hwf hpost hfresh hshape hnew hratio hi
      have hp := processReceipt_reward_backed cfg ap decoder st receipt hpost hshape hnew hratio
      have hsplit := receiptsFunds_filter_split cfg Receipt.isInstant (processReceipt cfg ap decoder st receipt).receipts
      refine ⟨hacc, hpost', ?_, hp, ?_⟩
      · intro x hx; exact (List.mem_filter.mp hx).2
      · have hP : (processReceipt cfg ap decoder st receipt).totalFunds cfg =
            (processReceipt cfg ap decoder st receipt).state.totalFunds cfg +
              receiptsFunds cfg (processReceipt cfg ap decoder st receipt).receipts := rfl
        have hnet : (processReceipt cfg ap decoder st receipt).netTokensBurnt =
            (processReceipt cfg ap decoder st receipt).grossTokensBurnt - (processReceipt cfg ap decoder st receipt).rewards := rfl
        change (processReceipt cfg ap decoder st receipt).totalFunds cfg + (processReceipt cfg ap decoder st receipt).netTokensBurnt = _ at hc
        change (processReceipt cfg ap decoder st receipt).state.totalFunds cfg +
          receiptsFunds cfg ((processReceipt cfg ap decoder st receipt).receipts.filter fun x => !x.isInstant) +
          receiptsFunds cfg ((processReceipt cfg ap decoder st receipt).receipts.filter Receipt.isInstant) +
          ((processReceipt cfg ap decoder st receipt).grossTokensBurnt - (processReceipt cfg ap decoder st receipt).rewards) =
          base + (processReceipt cfg ap decoder st receipt).subsidizedAmount
        omega)
    st receipt ⟨rfl, rfl⟩
  exact key hsupported

/-- The nested outcome loop followed by the real reward deduction adds precisely one receipt's
(and its instant receipts') net burn to the incoming ledger. -/
theorem processWithInstants_outcomeLoop_burn (cfg : RuntimeConfig) (ap : ApplyState)
    (decoder : Bytes → ContractCode) (st : ChainState) (receipt : Receipt) (prior gas : Nat)
    (hrewards : (processWithInstants cfg ap decoder st receipt).rewards ≤
      (processWithInstants cfg ap decoder st receipt).grossTokensBurnt) :
    let p := processWithInstants cfg ap decoder st receipt
    (forIn p.outcomes (prior, gas) (fun entry ledger =>
      pure (.yield (ledger.1 + entry.2.tokensBurnt, ledger.2 + entry.2.computeUsage))) : Id (Nat × Nat)).1 +
        p.otherTokensBurnt - p.rewards = prior + p.netTokensBurnt := by
  dsimp only
  rw [forIn_outcomes_tokensBurnt]
  dsimp only [Processed.netTokensBurnt, Processed.grossTokensBurnt] at hrewards ⊢
  omega

end Near
