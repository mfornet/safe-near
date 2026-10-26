import NearRuntime.MetadataFunding
import NearRuntime.RefundReceiptInvariants

namespace Near
open Wasm.Near

/-- Inserting an absent account adds exactly its liquid and locked balance. -/
theorem ChainState.totalBalance_newAccount (st : ChainState) (id : AccountId) (account : Account)
    (hwf : st.AccountsUnique) (hmissing : st.account? id = none) :
    (st.setAccount id account).totalBalance = st.totalBalance + account.amount + account.locked := by
  have hm := Assoc.mass_insert_accounting (fun a : Account => a.amount + a.locked) st.accounts id account hwf.accounts
  change Assoc.lookup st.accounts id = none at hmissing
  simp only [hmissing, Option.map_none, Option.getD_none, Nat.add_zero] at hm
  have hg := ChainState.gasKeyFunds_setAccount st id account
  unfold ChainState.totalBalance
  rw [hg]
  simp only [ChainState.setAccount, Assoc.mass] at hm ⊢
  omega

/-- Deposit credit with unchanged gas counters establishes the additive rule. -/
theorem Exec.FundingStep.of_deposit (cfg : RuntimeConfig) (price deposit : Nat) (before after : Exec)
    (hfunds : after.totalFunds cfg = before.totalFunds cfg + deposit)
    (hburn : after.gasBurnt = before.gasBurnt) (hused : after.gasUsed = before.gasUsed)
    (hsubsidy : after.subsidizedAmount = before.subsidizedAmount)
    (htokens : after.actionTokensBurnt = before.actionTokensBurnt := by rfl) :
    Exec.FundingStep cfg price deposit before after := by
  simp only [Exec.FundingStep, hfunds, hburn, hused, hsubsidy, htokens]

/-- A concrete successful result packages its state and funding witnesses. -/
theorem balance_return_funded (cfg : RuntimeConfig) (price deposit : Nat) (before after result : Exec)
    (value : Unit) (hwf : result.state.AccountsUnique)
    (hfunds : result.totalFunds cfg = before.totalFunds cfg + deposit)
    (hburn : result.gasBurnt = before.gasBurnt) (hused : result.gasUsed = before.gasUsed)
    (hsubsidy : result.subsidizedAmount = before.subsidizedAmount)
    (hrun : ((.ok (), result) : Except RuntimeError Unit × Exec) = (.ok value, after))
    (htokens : result.actionTokensBurnt = before.actionTokensBurnt := by rfl) :
    after.state.AccountsUnique ∧ Exec.FundingStep cfg price deposit before after := by
  have he := congrArg Prod.snd hrun
  dsimp only at he
  subst after
  exact ⟨hwf, Exec.FundingStep.of_deposit cfg price deposit before result hfunds hburn hused hsubsidy htokens⟩

/-- Creation starts the account with no liquid or locked funds. -/
theorem applyCreateAccount_run (c : ReceiptCtx) (isLast : Bool) (before : Exec) :
    (applyAction c isLast .createAccount).run.run before =
      if (before.state.account? c.receipt.receiverId).isSome then
        (.error (.accountAlreadyExists c.receipt.receiverId), before)
      else if canCreateAccount c.cfg c.receipt.predecessorId c.receipt.receiverId then
        (.ok (), { before with state := before.state.setAccount c.receipt.receiverId { amount := 0, storageUsage := c.cfg.fees.numBytesAccount }, actorId := c.receipt.receiverId })
      else if c.receipt.receiverId != systemAccount && (c.receipt.receiverId.splitOn ".").length == 1 then
        (.error (.createAccountOnlyByRegistrar c.receipt.receiverId c.cfg.accountCreation.registrarAccountId c.receipt.predecessorId), before)
      else (.error (.createAccountNotAllowed c.receipt.receiverId c.receipt.predecessorId), before) := by
  by_cases ha : (before.state.account? c.receipt.receiverId).isSome = true
  · simp [-StateT.run_bind, applyAction, getState, ha]
  · by_cases hc : canCreateAccount c.cfg c.receipt.predecessorId c.receipt.receiverId = true <;>
      simp [-StateT.run_bind, applyAction, getState, putAccount, modifyState, ha, hc]
    split <;> rfl

/-- An absent reserved actor cannot acquire an account through actual creation.
The result is a protocol admission error and preserves the pre-action state. -/
theorem applyCreateAccount_system_missing (c : ReceiptCtx) (isLast : Bool) (before : Exec)
    (hreceiver : c.receipt.receiverId = systemAccount) (hmissing : before.state.account? systemAccount = none) :
    (applyAction c isLast .createAccount).run.run before =
      (.error (.createAccountNotAllowed systemAccount c.receipt.predecessorId), before) := by
  rw [applyCreateAccount_run]
  simp [hreceiver, hmissing]

theorem funded_createAccount (c : ReceiptCtx) (isLast : Bool) :
    (applyAction c isLast .createAccount).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyCreateAccount_run] at hrun
  cases ha : before.state.account? c.receipt.receiverId with
  | some account =>
    simp only [ha, Option.isSome_some, ite_true] at hrun
    have hbad := congrArg Prod.fst hrun; cases hbad
  | none =>
    simp only [ha, Option.isSome_none, Bool.false_eq_true, ite_false] at hrun
    split at hrun
    · apply balance_return_funded c.cfg c.action.gasPrice 0 before after _ value ?_ ?_ ?_ ?_ ?_ hrun
      · exact hwf.setAccount _ _
      · have hb := before.state.totalBalance_newAccount c.receipt.receiverId
          { amount := 0, storageUsage := c.cfg.fees.numBytesAccount } hwf ha
        simpa only [Exec.totalFunds, Nat.add_zero] using congrArg (fun n => n + receiptsFunds c.cfg before.newReceipts) hb
      all_goals rfl
    · split at hrun <;> (have hbad := congrArg Prod.fst hrun; cases hbad)

/-- The real existing-account transfer includes any gas-refund allowance update. -/
def transferCreditState (c : ReceiptCtx) (st : ChainState) (account : Account) (deposit : Nat) : ChainState :=
  let credited := st.setAccount c.receipt.receiverId { account with amount := account.amount + deposit }
  if c.receipt.isGasRefund then credited.refundAllowance c.receipt.receiverId c.action.signerPublicKey deposit else credited

/-- Implicit creation installs the exact account/key storage metadata. -/
def implicitTransferState (c : ReceiptCtx) (st : ChainState) (pk : PublicKey) (deposit : Nat) : ChainState :=
  let key : AccessKey := { nonce := initialNonce c.ap.blockHeight, permission := .fullAccess }
  let account : Account := { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount + accessKeyStorageBytes pk key + c.cfg.fees.numExtraBytesRecord }
  (st.setAccount c.receipt.receiverId account).setAccessKey c.receipt.receiverId pk key

theorem applyTransfer_run (c : ReceiptCtx) (isLast : Bool) (deposit : Nat) (before : Exec) :
    (applyAction c isLast (.transfer deposit)).run.run before =
      match before.state.account? c.receipt.receiverId with
      | some account => (.ok (), { before with state := transferCreditState c before.state account deposit })
      | none =>
        match specialImplicitAccount c c.receipt.receiverId deposit with
        | .error e => (.error e, before)
        | .ok (some account) =>
          (.ok (), { before with state := before.state.setAccount c.receipt.receiverId account, actorId := c.receipt.receiverId })
        | .ok none =>
          match implicitPublicKey? c.receipt.receiverId with
          | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
          | some pk => (.ok (), { before with state := implicitTransferState c before.state pk deposit, actorId := c.receipt.receiverId }) := by
  cases ha : before.state.account? c.receipt.receiverId with
  | some account =>
    by_cases hr : c.receipt.isGasRefund = true <;>
      simp [-StateT.run_bind, applyAction, getState, putAccount, modifyState, ha, transferCreditState, hr]
  | none =>
    cases hs : specialImplicitAccount c c.receipt.receiverId deposit with
    | error e => simp [-StateT.run_bind, applyAction, getState, liftExcept, ha, hs]
    | ok special =>
      cases special with
      | some account =>
        simp [-StateT.run_bind, applyAction, getState, liftExcept, putAccount, modifyState, ha, hs]
      | none =>
        cases hp : implicitPublicKey? c.receipt.receiverId <;>
          simp [-StateT.run_bind, applyAction, getState, liftExcept, putAccount, modifyState, ha, hs, hp,
            implicitTransferState]

theorem specialImplicitAccount_amount {c : ReceiptCtx} {id : AccountId} {deposit : Nat} {account : Account}
    (h : specialImplicitAccount c id deposit = .ok (some account)) :
    account.amount = deposit ∧ account.locked = 0 := by
  unfold specialImplicitAccount at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact ⟨rfl, rfl⟩)

/-- Ordinary transfer and best-effort refund-allowance restoration preserve
exact deposit funding; implicit creation adds the same deposit exactly once. -/
theorem funded_transfer (c : ReceiptCtx) (isLast : Bool) (deposit : Nat) :
    (applyAction c isLast (.transfer deposit)).Funded c.cfg c.action.gasPrice deposit := by
  intro before after value hwf hrun
  rw [applyTransfer_run] at hrun
  cases ha : before.state.account? c.receipt.receiverId with
  | some account =>
    simp only [ha] at hrun
    apply balance_return_funded c.cfg c.action.gasPrice deposit before after _ value ?_ ?_ ?_ ?_ ?_ hrun
    · exact refundTransferState_accountsUnique c before.state account deposit hwf
    · change (refundTransferState c before.state account deposit).totalBalance + receiptsFunds c.cfg before.newReceipts =
        before.state.totalBalance + receiptsFunds c.cfg before.newReceipts + deposit
      rw [refundTransferState_totalBalance c before.state account deposit hwf ha]
      omega
    all_goals rfl
  | none =>
    simp only [ha] at hrun
    cases hs : specialImplicitAccount c c.receipt.receiverId deposit with
    | error e => simp only [hs] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
    | ok special =>
      cases special with
      | some account =>
        simp only [hs] at hrun
        have hv := specialImplicitAccount_amount hs
        apply balance_return_funded c.cfg c.action.gasPrice deposit before after _ value ?_ ?_ ?_ ?_ ?_ hrun
        · exact hwf.setAccount _ _
        · unfold Exec.totalFunds
          have hb := before.state.totalBalance_newAccount c.receipt.receiverId account hwf ha
          change (before.state.setAccount c.receipt.receiverId account).totalBalance +
            receiptsFunds c.cfg before.newReceipts = _
          rw [hb, hv.1, hv.2]
          omega
        all_goals rfl
      | none =>
        simp only [hs] at hrun
        cases hp : implicitPublicKey? c.receipt.receiverId with
        | none =>
          simp only [hp] at hrun
          have hbad := congrArg Prod.fst hrun; cases hbad
        | some pk =>
          simp only [hp] at hrun
          apply balance_return_funded c.cfg c.action.gasPrice deposit before after _ value ?_ ?_ ?_ ?_ ?_ hrun
          · exact ChainState.accountsUnique_setAccount_new_key hwf _ _ _ _
          · unfold Exec.totalFunds
            have hk := ChainState.accessKey_none_of_account_none hwf c.receipt.receiverId pk ha
            change ((before.state.setAccount c.receipt.receiverId _).setAccessKey c.receipt.receiverId pk _).totalBalance +
              receiptsFunds c.cfg before.newReceipts = _
            rw [ChainState.totalBalance_setAccessKey_new _ _ _ _ (hwf.setAccount _ _)
              (by exact hk) (by simp [AccessKey.gasBalance, AccessKeyPermission.gasKeyInfo?])]
            have hb := before.state.totalBalance_newAccount c.receipt.receiverId
              { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount +
                  accessKeyStorageBytes pk { nonce := initialNonce c.ap.blockHeight, permission := .fullAccess } + c.cfg.fees.numExtraBytesRecord } hwf ha
            dsimp only at hb
            rw [hb]
            omega
          all_goals rfl

/-- The deletion result retains the actual refund receipt and fresh id while removing the
receiver and its keys from the state, and burns what the receiver's gas keys held. -/
def deleteAccountFundedResult (c : ReceiptCtx) (before : Exec) (account : Account) (beneficiary : AccountId) : Exec :=
  let id := c.receipt.receiverId
  let refund := refundReceipt before.state beneficiary account.amount
  let cleared : Exec := { before with
    state := refund.2.removeAccount id
    storageAccounting := stageContractStorageRemoval id (refund.2.contractStorage id) before.storageAccounting }
  let burned := cleared.burnAction (before.state.gasKeyBalances id)
    (nonceRemovalCompute c.cfg ((before.state.gasKeyNonces.filter (·.1.1 == id)).map fun ((id, pk, _), _) => (id, pk)))
  let acted : Exec := { burned with actorId := c.receipt.predecessorId }
  if account.amount > 0 then { acted with newReceipts := acted.newReceipts ++ [refund.1] } else acted

/-- The bytes of the receiver's contract that do not count towards the storage left at deletion. -/
def deleteAccountContractBytes (c : ReceiptCtx) (account : Account) : Nat :=
  if c.cfg.fixDeleteAccountGlobalContractStorageUsage then account.contractStorageUsage
  else (account.code.map (·.size)).getD 0

theorem deleteAccountFundedResult_advance (c : ReceiptCtx) (before : Exec) (account : Account)
    (beneficiary : AccountId) :
    before.state.RoutingAdvance (deleteAccountFundedResult c before account beneficiary).state := by
  unfold deleteAccountFundedResult
  dsimp only
  split
  · exact (ChainState.RoutingAdvance.freshId _).trans (ChainState.RoutingAdvance.of_routing rfl)
  · exact (ChainState.RoutingAdvance.freshId _).trans (ChainState.RoutingAdvance.of_routing rfl)

theorem applyDeleteAccount_run (c : ReceiptCtx) (isLast : Bool) (beneficiary : AccountId) (before : Exec) :
    (applyAction c isLast (.deleteAccount beneficiary)).run.run before =
      if !isLast then (.error .deleteActionMustBeFinal, before)
      else match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account =>
          if account.locked > 0 then (.error (.deleteAccountStaking c.receipt.receiverId), before)
          else if account.storageUsage - deleteAccountContractBytes c account > maxAccountDeletionStorageUsage then
            (.error (.deleteAccountWithLargeState c.receipt.receiverId), before)
          else if before.state.gasKeyBalances c.receipt.receiverId > maxGasKeyBalanceToBurn then
            (.error (.gasKeyBalanceTooHigh c.receipt.receiverId none (before.state.gasKeyBalances c.receipt.receiverId)),
              before)
          else (.ok (), deleteAccountFundedResult c before account beneficiary) := by
  by_cases hl : isLast = true
  · cases ha : before.state.account? c.receipt.receiverId with
    | none => simp [-StateT.run_bind, applyAction, getAccount, getState, hl, ha]
    | some account =>
      by_cases hlock : account.locked > 0
      · simp [-StateT.run_bind, applyAction, getAccount, getState, hl, ha, hlock]
      · by_cases hlarge : account.storageUsage - deleteAccountContractBytes c account > maxAccountDeletionStorageUsage
        · have hlarge' := hlarge
          simp only [deleteAccountContractBytes, gt_iff_lt] at hlarge'
          simp [-StateT.run_bind, applyAction, getAccount, getState, hl, ha, hlock, hlarge',
            deleteAccountContractBytes]
        · have hlarge' := hlarge
          simp only [deleteAccountContractBytes, gt_iff_lt] at hlarge'
          by_cases hkeys : before.state.gasKeyBalances c.receipt.receiverId > maxGasKeyBalanceToBurn
          · simp [-StateT.run_bind, applyAction, getAccount, getState, hl, ha, hlock, hlarge', hkeys,
              deleteAccountContractBytes]
          · by_cases hpos : account.amount > 0 <;>
              simp [-StateT.run_bind, applyAction, getAccount, getState, hl, ha, hlock, hlarge', hkeys, hpos,
                deleteAccountFundedResult, Exec.burnAction, emit, deleteAccountContractBytes]
  · simp [-StateT.run_bind, applyAction, hl]

/-- Deletion funds the beneficiary refund by removing precisely the unlocked receiver balance
and burning the balance of its gas keys. A positive locked balance is rejected by the executable
guard. -/
theorem deleteAccountFundedResult_funds (c : ReceiptCtx) (before : Exec) (account : Account) (beneficiary : AccountId)
    (hwf : before.state.AccountsUnique) (ha : before.state.account? c.receipt.receiverId = some account)
    (hlocked : account.locked = 0) :
    (deleteAccountFundedResult c before account beneficiary).totalFunds c.cfg +
      before.state.gasKeyBalances c.receipt.receiverId = before.totalFunds c.cfg := by
  let refund := refundReceipt before.state beneficiary account.amount
  have hwu : refund.2.AccountsUnique := hwf
  have hlookup : refund.2.account? c.receipt.receiverId = some account := ha
  have hb := refund.2.totalBalance_removeAccount c.receipt.receiverId account hwu hlookup
  rw [hlocked, Nat.add_zero] at hb
  have hgk : refund.2.gasKeyBalances c.receipt.receiverId = before.state.gasKeyBalances c.receipt.receiverId := rfl
  have htb : refund.2.totalBalance = before.state.totalBalance := rfl
  have hr : Fees.receiptFunds c.cfg refund.1 = account.amount := by
    simp [refund, refundReceipt, Fees.receiptFunds, Fees.totalDeposit, Action.deposit, Receipt.isRefund]
  unfold deleteAccountFundedResult Exec.totalFunds
  dsimp only
  by_cases hpos : account.amount > 0
  · simp only [hpos, ite_true, Exec.burnAction, receiptsFunds_append]
    have hrf : receiptsFunds c.cfg [refund.1] = account.amount := by simp [receiptsFunds, hr]
    change (refund.2.removeAccount c.receipt.receiverId).totalBalance +
      (receiptsFunds c.cfg before.newReceipts + receiptsFunds c.cfg [refund.1]) +
        before.state.gasKeyBalances c.receipt.receiverId = before.state.totalBalance + receiptsFunds c.cfg before.newReceipts
    omega
  · have hz : account.amount = 0 := by omega
    simp only [hpos, ite_false, Exec.burnAction]
    change (refund.2.removeAccount c.receipt.receiverId).totalBalance + receiptsFunds c.cfg before.newReceipts +
      before.state.gasKeyBalances c.receipt.receiverId = before.state.totalBalance + receiptsFunds c.cfg before.newReceipts
    omega

theorem deleteAccountFundedResult_fields (c : ReceiptCtx) (before : Exec) (account : Account) (beneficiary : AccountId) :
    (deleteAccountFundedResult c before account beneficiary).gasBurnt = before.gasBurnt ∧
    (deleteAccountFundedResult c before account beneficiary).gasUsed = before.gasUsed ∧
    (deleteAccountFundedResult c before account beneficiary).subsidizedAmount = before.subsidizedAmount ∧
    (deleteAccountFundedResult c before account beneficiary).actionTokensBurnt =
      before.actionTokensBurnt + before.state.gasKeyBalances c.receipt.receiverId := by
  unfold deleteAccountFundedResult
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem deleteAccountFundedResult_accountsUnique (c : ReceiptCtx) (before : Exec) (account : Account)
    (beneficiary : AccountId) (hwf : before.state.AccountsUnique) :
    (deleteAccountFundedResult c before account beneficiary).state.AccountsUnique := by
  unfold deleteAccountFundedResult
  dsimp only
  split <;> exact (show (refundReceipt before.state beneficiary account.amount).2.AccountsUnique from hwf).removeAccount _

theorem funded_deleteAccount (c : ReceiptCtx) (isLast : Bool) (beneficiary : AccountId) :
    (applyAction c isLast (.deleteAccount beneficiary)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyDeleteAccount_run] at hrun
  split at hrun
  · have hbad := congrArg Prod.fst hrun; cases hbad
  · cases ha : before.state.account? c.receipt.receiverId with
    | none =>
      simp only [ha] at hrun
      have hbad := congrArg Prod.fst hrun; cases hbad
    | some account =>
      simp only [ha] at hrun
      split at hrun
      · have hbad := congrArg Prod.fst hrun; cases hbad
      · rename_i hlocked
        split at hrun
        · have hbad := congrArg Prod.fst hrun; cases hbad
        · split at hrun
          · have hbad := congrArg Prod.fst hrun; cases hbad
          · have he := congrArg Prod.snd hrun
            dsimp only at he
            subst after
            have hfunds := deleteAccountFundedResult_funds c before account beneficiary hwf ha (by omega)
            have hfields := deleteAccountFundedResult_fields c before account beneficiary
            refine ⟨?_, Exec.FundingStep.of_burn c.cfg c.action.gasPrice (before.state.gasKeyBalances c.receipt.receiverId)
              before _ hfunds hfields.1 hfields.2.1 hfields.2.2.1 hfields.2.2.2⟩
            exact deleteAccountFundedResult_accountsUnique c before account beneficiary hwf

end Near
