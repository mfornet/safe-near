import NearRuntime.ActionFunding

namespace Near
open Wasm.Near

/-- A metadata-only action retains the financial and gas observations used by
funding composition; account and key storage can still change. -/
theorem Exec.FundingStep.of_fields (cfg : RuntimeConfig) (price : Nat) (before after : Exec)
    (hfunds : after.totalFunds cfg = before.totalFunds cfg)
    (hburn : after.gasBurnt = before.gasBurnt) (hused : after.gasUsed = before.gasUsed)
    (hsubsidy : after.subsidizedAmount = before.subsidizedAmount) :
    Exec.FundingStep cfg price 0 before after := by
  simp only [Exec.FundingStep, hfunds, hburn, hused, hsubsidy, Nat.add_zero]

/-- Replacing account metadata preserves liquid plus locked funds. The current
account lookup and uniqueness premises prevent hidden duplicate-account mass. -/
theorem ChainState.totalBalance_metadata (st : ChainState) (id : AccountId) (old replacement : Account)
    (hwf : st.AccountsUnique) (haccount : st.account? id = some old)
    (hamount : replacement.amount = old.amount) (hlocked : replacement.locked = old.locked) :
    (st.setAccount id replacement).totalBalance = st.totalBalance := by
  have hb := st.totalBalance_setAccount id replacement old hwf haccount
  rw [hamount, hlocked] at hb
  omega

/-- Executable deployment unfolding, preserving the account witness used by
metadata accounting instead of expanding the whole action interpreter. -/
theorem applyDeployContract_run (c : ReceiptCtx) (isLast : Bool) (code : ContractCode) (before : Exec) :
    (applyAction c isLast (.deployContract code)).run.run before =
      match code.decodeIssue with
      | some issue => (.error (.executionIssue issue), before)
      | none =>
        match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account =>
          if code.size > c.cfg.wasm.limits.maxContractSize then
            (.error (.contractSizeExceeded code.size c.cfg.wasm.limits.maxContractSize), before)
          else (.ok (), { before with state := before.state.setAccount c.receipt.receiverId { account with code := some code, storageUsage := account.storageUsage + code.size - (account.code.map (·.size)).getD 0 } }) := by
  cases hd : code.decodeIssue with
  | some issue => simp [-StateT.run_bind, applyAction, hd]
  | none =>
    cases ha : before.state.account? c.receipt.receiverId with
    | none => simp [-StateT.run_bind, applyAction, hd, getAccount, getState, ha]
    | some account =>
      by_cases hs : code.size > c.cfg.wasm.limits.maxContractSize <;>
        simp [-StateT.run_bind, applyAction, hd, getAccount, getState, putAccount, modifyState, ha, hs]

/-- Deployment changes code/storage metadata, with no balance or gas side
channel. Fees are charged separately by `runReceiptAction`. -/
theorem funded_deployContract (c : ReceiptCtx) (isLast : Bool) (code : ContractCode) :
    (applyAction c isLast (.deployContract code)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyDeployContract_run] at hrun
  cases hd : code.decodeIssue with
  | some issue =>
    simp only [hd] at hrun
    have hbad := congrArg Prod.fst hrun
    cases hbad
  | none =>
    simp only [hd] at hrun
    cases ha : before.state.account? c.receipt.receiverId with
    | none =>
      simp only [ha] at hrun
      have hbad := congrArg Prod.fst hrun
      cases hbad
    | some account =>
      simp only [ha] at hrun
      split at hrun
      · have hbad := congrArg Prod.fst hrun; cases hbad
      · have he := congrArg Prod.snd hrun
        dsimp only at he
        subst after
        refine ⟨hwf.setAccount _ _, Exec.FundingStep.of_fields c.cfg c.action.gasPrice before _ ?_ rfl rfl rfl⟩
        unfold Exec.totalFunds
        dsimp only
        congr 1
        apply ChainState.totalBalance_metadata _ _ account
        · exact hwf
        · exact ha
        · rfl
        · rfl

/-- Success-state accounting for an action that changes only chain metadata. -/
theorem metadata_return_funded (cfg : RuntimeConfig) (price : Nat) (before after : Exec)
    (value : Unit) (next : ChainState) (hwf : next.AccountsUnique)
    (hbalance : next.totalBalance = before.state.totalBalance)
    (hrun : ((.ok (), { before with state := next }) : Except RuntimeError Unit × Exec) = (.ok value, after)) :
    after.state.AccountsUnique ∧ Exec.FundingStep cfg price 0 before after := by
  have he := congrArg Prod.snd hrun
  dsimp only at he
  subst after
  refine ⟨hwf, Exec.FundingStep.of_fields cfg price before _ ?_ rfl rfl rfl⟩
  exact congrArg (fun balance => balance + receiptsFunds cfg before.newReceipts) hbalance

def addKeyMetadataState (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey) (key : AccessKey) : ChainState :=
  let updated := { account with storageUsage := account.storageUsage + accessKeyStorageBytes pk key + c.cfg.fees.numExtraBytesRecord }
  (st.setAccount c.receipt.receiverId updated).setAccessKey c.receipt.receiverId pk { key with nonce := initialNonce c.ap.blockHeight }

def deleteKeyMetadataState (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey) (key : AccessKey) : ChainState :=
  let updated := { account with storageUsage := account.storageUsage - (accessKeyStorageBytes pk key + c.cfg.fees.numExtraBytesRecord) }
  (st.setAccount c.receipt.receiverId updated).removeAccessKey c.receipt.receiverId pk

/-- Key insertion updates permission/storage metadata after duplicate-key and
account admission checks, and preserves every execution counter. -/
theorem applyAddKey_run (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (key : AccessKey) (before : Exec) :
    (applyAction c isLast (.addKey pk key)).run.run before =
      if (before.state.accessKey? c.receipt.receiverId pk).isSome then
        (.error (.addKeyAlreadyExists c.receipt.receiverId pk), before)
      else match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account => (.ok (), { before with state := addKeyMetadataState c before.state account pk key }) := by
  by_cases hk : (before.state.accessKey? c.receipt.receiverId pk).isSome = true
  · simp [-StateT.run_bind, applyAction, getState, hk]
  · cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, addKeyMetadataState]

theorem applyDeleteKey_run (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (before : Exec) :
    (applyAction c isLast (.deleteKey pk)).run.run before =
      match before.state.accessKey? c.receipt.receiverId pk with
      | none => (.error (.deleteKeyDoesNotExist c.receipt.receiverId pk), before)
      | some key => match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account => (.ok (), { before with state := deleteKeyMetadataState c before.state account pk key }) := by
  cases hk : before.state.accessKey? c.receipt.receiverId pk with
  | none => simp [-StateT.run_bind, applyAction, getState, hk]
  | some key =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, deleteKeyMetadataState]

theorem funded_addKey (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (key : AccessKey) :
    (applyAction c isLast (.addKey pk key)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyAddKey_run] at hrun
  split at hrun
  · have hbad := congrArg Prod.fst hrun; cases hbad
  · cases ha : before.state.account? c.receipt.receiverId with
    | none =>
      simp only [ha] at hrun
      have hbad := congrArg Prod.fst hrun; cases hbad
    | some account =>
      simp only [ha] at hrun
      apply metadata_return_funded c.cfg c.action.gasPrice before after value _ ?_ ?_ hrun
      · exact hwf.setAccount _ _
      · change (before.state.setAccount c.receipt.receiverId _).totalBalance = before.state.totalBalance
        apply ChainState.totalBalance_metadata _ _ account
        · exact hwf
        · exact ha
        · rfl
        · rfl

theorem funded_deleteKey (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) :
    (applyAction c isLast (.deleteKey pk)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyDeleteKey_run] at hrun
  cases hk : before.state.accessKey? c.receipt.receiverId pk with
  | none =>
    simp only [hk] at hrun
    have hbad := congrArg Prod.fst hrun; cases hbad
  | some key =>
    simp only [hk] at hrun
    cases ha : before.state.account? c.receipt.receiverId with
    | none =>
      simp only [ha] at hrun
      have hbad := congrArg Prod.fst hrun; cases hbad
    | some account =>
      simp only [ha] at hrun
      apply metadata_return_funded c.cfg c.action.gasPrice before after value _ ?_ ?_ hrun
      · exact hwf.setAccount _ _
      · change (before.state.setAccount c.receipt.receiverId _).totalBalance = before.state.totalBalance
        apply ChainState.totalBalance_metadata _ _ account
        · exact hwf
        · exact ha
        · rfl
        · rfl

end Near
