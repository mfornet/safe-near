import NearRuntime.MetadataFunding
import NearRuntime.RefundReceiptInvariants

namespace Near
open Wasm.Near

/-- Inserting an absent account adds exactly its liquid and locked balance. -/
theorem ChainState.totalBalance_newAccount (st : ChainState) (id : AccountId) (account : Account)
    (hwf : st.AccountsUnique) (hmissing : st.account? id = none) :
    (st.setAccount id account).totalBalance = st.totalBalance + account.amount + account.locked := by
  have hm := Assoc.mass_insert_accounting (fun a : Account => a.amount + a.locked) st.accounts id account hwf
  change Assoc.lookup st.accounts id = none at hmissing
  simpa only [hmissing, Option.map_none, Option.getD_none, Nat.add_zero, ChainState.totalBalance,
    ChainState.setAccount, Assoc.mass, Nat.add_assoc] using hm

/-- Deposit credit with unchanged gas counters establishes the additive rule. -/
theorem Exec.FundingStep.of_deposit (cfg : RuntimeConfig) (price deposit : Nat) (before after : Exec)
    (hfunds : after.totalFunds cfg = before.totalFunds cfg + deposit)
    (hburn : after.gasBurnt = before.gasBurnt) (hused : after.gasUsed = before.gasUsed)
    (hsubsidy : after.subsidizedAmount = before.subsidizedAmount) :
    Exec.FundingStep cfg price deposit before after := by
  simp only [Exec.FundingStep, hfunds, hburn, hused, hsubsidy]

/-- A concrete successful result packages its state and funding witnesses. -/
theorem balance_return_funded (cfg : RuntimeConfig) (price deposit : Nat) (before after result : Exec)
    (value : Unit) (hwf : result.state.AccountsUnique)
    (hfunds : result.totalFunds cfg = before.totalFunds cfg + deposit)
    (hburn : result.gasBurnt = before.gasBurnt) (hused : result.gasUsed = before.gasUsed)
    (hsubsidy : result.subsidizedAmount = before.subsidizedAmount)
    (hrun : ((.ok (), result) : Except RuntimeError Unit × Exec) = (.ok value, after)) :
    after.state.AccountsUnique ∧ Exec.FundingStep cfg price deposit before after := by
  have he := congrArg Prod.snd hrun
  dsimp only at he
  subst after
  exact ⟨hwf, Exec.FundingStep.of_deposit cfg price deposit before result hfunds hburn hused hsubsidy⟩

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
        if unsupportedImplicitCreation c.cfg.wasm.ethImplicitAccounts (bytesOfString c.receipt.receiverId) then
          (.error (.executionIssue (.unsupportedAction "implicit account creation (ETH/deterministic contracts)")), before)
        else match implicitPublicKey? c.receipt.receiverId with
          | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
          | some pk => (.ok (), { before with state := implicitTransferState c before.state pk deposit, actorId := c.receipt.receiverId }) := by
  cases ha : before.state.account? c.receipt.receiverId with
  | some account =>
    by_cases hr : c.receipt.isGasRefund = true <;>
      simp [-StateT.run_bind, applyAction, getState, putAccount, modifyState, ha, transferCreditState, hr]
  | none =>
    by_cases hu : unsupportedImplicitCreation c.cfg.wasm.ethImplicitAccounts (bytesOfString c.receipt.receiverId) = true
    · simp [-StateT.run_bind, applyAction, getState, ha, hu]
    · cases hp : implicitPublicKey? c.receipt.receiverId <;>
        simp [-StateT.run_bind, applyAction, getState, putAccount, modifyState, ha, hu, hp, implicitTransferState]

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
    split at hrun
    · have hbad := congrArg Prod.fst hrun; cases hbad
    · cases hp : implicitPublicKey? c.receipt.receiverId with
      | none =>
        simp only [hp] at hrun
        have hbad := congrArg Prod.fst hrun; cases hbad
      | some pk =>
        simp only [hp] at hrun
        apply balance_return_funded c.cfg c.action.gasPrice deposit before after _ value ?_ ?_ ?_ ?_ ?_ hrun
        · exact hwf.setAccount _ _
        · unfold Exec.totalFunds
          change (before.state.setAccount c.receipt.receiverId _).totalBalance + receiptsFunds c.cfg before.newReceipts = _
          have hb := before.state.totalBalance_newAccount c.receipt.receiverId
            { amount := deposit, storageUsage := c.cfg.fees.numBytesAccount +
                accessKeyStorageBytes pk { nonce := initialNonce c.ap.blockHeight, permission := .fullAccess } + c.cfg.fees.numExtraBytesRecord } hwf ha
          dsimp only at hb
          rw [hb]
          omega
        all_goals rfl

/-- The deletion result retains the actual refund receipt and fresh id, when
there is a balance to pay out, while removing the receiver's liquid balance
from the account map. -/
def deleteAccountFundedResult (c : ReceiptCtx) (before : Exec) (account : Account) (beneficiary : AccountId) : Exec :=
  let refunded := if account.amount > 0 then before.addBalanceRefund beneficiary account.amount else before
  { refunded with
    state := refunded.state.removeAccount c.receipt.receiverId
    actorId := c.receipt.predecessorId
    storageAccounting := stageContractStorageRemoval c.receipt.receiverId
      (refunded.state.contractStorage c.receipt.receiverId) refunded.storageAccounting }

theorem applyDeleteAccount_run (c : ReceiptCtx) (isLast : Bool) (beneficiary : AccountId) (before : Exec) :
    (applyAction c isLast (.deleteAccount beneficiary)).run.run before =
      if !isLast then (.error .deleteActionMustBeFinal, before)
      else match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account =>
          if account.locked > 0 then (.error (.deleteAccountStaking c.receipt.receiverId), before)
          else (.ok (), deleteAccountFundedResult c before account beneficiary) := by
  cases isLast with
  | false => simp [-StateT.run_bind, applyAction]
  | true =>
    cases ha : before.state.account? c.receipt.receiverId with
    | none => simp [-StateT.run_bind, applyAction, getAccount, getState, ha]
    | some account =>
      by_cases hl : account.locked > 0 <;> by_cases hamount : account.amount > 0 <;>
        simp [-StateT.run_bind, applyAction, getAccount, getState, emit, ha, hl, hamount,
          deleteAccountFundedResult, Exec.addBalanceRefund]

/-- Deletion funds the beneficiary refund by removing precisely the unlocked
receiver balance. A positive locked balance is rejected by the executable guard. -/
theorem deleteAccountFundedResult_funds (c : ReceiptCtx) (before : Exec) (account : Account) (beneficiary : AccountId)
    (hwf : before.state.AccountsUnique) (ha : before.state.account? c.receipt.receiverId = some account)
    (hlocked : account.locked = 0) :
    (deleteAccountFundedResult c before account beneficiary).totalFunds c.cfg = before.totalFunds c.cfg := by
  let refunded := if account.amount > 0 then before.addBalanceRefund beneficiary account.amount else before
  have hstate : refunded.state.account? c.receipt.receiverId = before.state.account? c.receipt.receiverId ∧
      refunded.state.AccountsUnique = before.state.AccountsUnique := by
    dsimp only [refunded]; split <;> exact ⟨rfl, rfl⟩
  have hwu : refunded.state.AccountsUnique := hstate.2 ▸ hwf
  have hlookup : refunded.state.account? c.receipt.receiverId = some account := hstate.1.trans ha
  have hb := refunded.state.totalBalance_removeAccount c.receipt.receiverId account hwu hlookup
  rw [hlocked, Nat.add_zero] at hb
  have hf : refunded.totalFunds c.cfg = before.totalFunds c.cfg + account.amount := by
    dsimp only [refunded]
    split
    · exact addBalanceRefund_totalFunds c.cfg before beneficiary account.amount
    · omega
  unfold Exec.totalFunds at hf ⊢
  change (refunded.state.removeAccount c.receipt.receiverId).totalBalance + receiptsFunds c.cfg refunded.newReceipts = _
  omega

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
        apply balance_return_funded c.cfg c.action.gasPrice 0 before after _ value ?_ ?_ ?_ ?_ ?_ hrun
        · unfold deleteAccountFundedResult; split <;> exact hwf.removeAccount _
        · simpa only [Nat.add_zero] using deleteAccountFundedResult_funds c before account beneficiary hwf ha (by omega)
        all_goals (unfold deleteAccountFundedResult; split <;> rfl)

end Near
