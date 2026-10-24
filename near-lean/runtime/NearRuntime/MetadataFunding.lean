import NearRuntime.ActionFunding
import NearRuntime.NewActionRun

namespace Near
open Wasm.Near

/-- A metadata-only action retains the financial and gas observations used by
funding composition; account and key storage can still change. -/
theorem Exec.FundingStep.of_fields (cfg : RuntimeConfig) (price : Nat) (before after : Exec)
    (hfunds : after.totalFunds cfg = before.totalFunds cfg)
    (hburn : after.gasBurnt = before.gasBurnt) (hused : after.gasUsed = before.gasUsed)
    (hsubsidy : after.subsidizedAmount = before.subsidizedAmount)
    (htokens : after.actionTokensBurnt = before.actionTokensBurnt := by rfl) :
    Exec.FundingStep cfg price 0 before after := by
  simp only [Exec.FundingStep, hfunds, hburn, hused, hsubsidy, htokens, Nat.add_zero]

/-- Replacing account metadata preserves liquid plus locked funds. The current
account lookup and uniqueness premises prevent hidden duplicate-account mass. -/
theorem ChainState.totalBalance_metadata (st : ChainState) (id : AccountId) (old replacement : Account)
    (hwf : st.AccountsUnique) (haccount : st.account? id = some old)
    (hamount : replacement.amount = old.amount) (hlocked : replacement.locked = old.locked) :
    (st.setAccount id replacement).totalBalance = st.totalBalance := by
  have hb := st.totalBalance_setAccount id replacement old hwf haccount
  rw [hamount, hlocked] at hb
  omega

/-- A step that burns tokens takes exactly that much out of the funds. -/
theorem Exec.FundingStep.of_burn (cfg : RuntimeConfig) (price burn : Nat) (before after : Exec)
    (hfunds : after.totalFunds cfg + burn = before.totalFunds cfg)
    (hburn : after.gasBurnt = before.gasBurnt) (hused : after.gasUsed = before.gasUsed)
    (hsubsidy : after.subsidizedAmount = before.subsidizedAmount)
    (htokens : after.actionTokensBurnt = before.actionTokensBurnt + burn) :
    Exec.FundingStep cfg price 0 before after := by
  simp only [Exec.FundingStep, hburn, hused, hsubsidy, htokens, Nat.add_zero]
  omega

/-- The account with its storage usage replaced. -/
def Account.withStorage (account : Account) (usage : Nat) : Account := { account with storageUsage := usage }

theorem ChainState.totalBalance_withStorage (st : ChainState) (id : AccountId) (account : Account) (usage : Nat)
    (hwf : st.AccountsUnique) (haccount : st.account? id = some account) :
    (st.setAccount id (account.withStorage usage)).totalBalance = st.totalBalance :=
  ChainState.totalBalance_metadata st id account _ hwf haccount rfl rfl

theorem ChainState.totalBalance_withStorage_remove (st : ChainState) (id : AccountId) (pk : PublicKey)
    (account : Account) (usage : Nat) (key : AccessKey)
    (hwf : st.AccountsUnique) (haccount : st.account? id = some account)
    (hk : st.accessKey? id pk = some key) :
    ((st.setAccount id (account.withStorage usage)).removeAccessKey id pk).totalBalance + key.gasBalance =
      st.totalBalance := by
  have hm := ChainState.totalBalance_withStorage st id account usage hwf haccount
  have hr := ChainState.totalBalance_removeAccessKey (st.setAccount id (account.withStorage usage)) id pk key
    (hwf.setAccount _ _) hk
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
          else
            let updated := { account with
              code := some code
              global := none
              storageUsage := (account.storageUsage - account.contractStorageUsage) + code.size }
            (.ok (), { before with state := before.state.setAccount c.receipt.receiverId updated }) := by
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
        refine ⟨hwf.setAccount _ _, Exec.FundingStep.of_fields c.cfg c.action.gasPrice before _ ?_ rfl rfl rfl rfl⟩
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
  refine ⟨hwf, Exec.FundingStep.of_fields cfg price before _ ?_ rfl rfl rfl rfl⟩
  exact congrArg (fun balance => balance + receiptsFunds cfg before.newReceipts) hbalance

/-- The state after adding a key: the account pays for the key's storage; a gas key also writes
its nonce lanes and starts with an empty balance. -/
def addKeyMetadataState (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey) (key : AccessKey) : ChainState :=
  let id := c.receipt.receiverId
  let extra := c.cfg.fees.numExtraBytesRecord
  match key.permission.gasKeyInfo? with
  | some (_, nonces) =>
    let stored : AccessKey := { key with nonce := 0, permission := key.permission.withGasBalance 0 }
    let usage := account.storageUsage + gasKeyStorageCost extra pk stored nonces
    (List.range nonces).foldl (fun st lane => st.setGasKeyNonce id pk lane (initialNonce c.ap.blockHeight))
      ((st.setAccount id (account.withStorage usage)).setAccessKey id pk stored)
  | none =>
    let usage := account.storageUsage + accessKeyStorageBytes pk key + extra
    (st.setAccount id (account.withStorage usage)).setAccessKey id pk
      { key with nonce := initialNonce c.ap.blockHeight }

/-- The state after deleting a key: the account is credited the key's storage; a gas key also
drops its nonce lanes. Its balance is burnt by the caller. -/
def deleteKeyMetadataState (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey) (key : AccessKey) : ChainState :=
  let id := c.receipt.receiverId
  let extra := c.cfg.fees.numExtraBytesRecord
  match key.permission.gasKeyInfo? with
  | some (_, nonces) =>
    let usage := account.storageUsage - gasKeyStorageCost extra pk key nonces
    ((st.setAccount id (account.withStorage usage)).removeAccessKey id pk).removeGasKeyNonces id pk
  | none =>
    let usage := account.storageUsage - (accessKeyStorageBytes pk key + extra)
    (st.setAccount id (account.withStorage usage)).removeAccessKey id pk

theorem ChainState.foldl_setGasKeyNonce_routing (id : AccountId) (pk : PublicKey) (nonce : Nat) (lanes : List Nat)
    (st : ChainState) :
    (lanes.foldl (fun st lane => st.setGasKeyNonce id pk lane nonce) st).routingState = st.routingState := by
  induction lanes generalizing st with
  | nil => rfl
  | cons lane rest ih => exact ih (st.setGasKeyNonce id pk lane nonce)

theorem addKeyMetadataState_routing (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey)
    (key : AccessKey) : (addKeyMetadataState c st account pk key).routingState = st.routingState := by
  unfold addKeyMetadataState
  split
  · exact ChainState.foldl_setGasKeyNonce_routing _ _ _ _ _
  · rfl

theorem deleteKeyMetadataState_routing (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey)
    (key : AccessKey) : (deleteKeyMetadataState c st account pk key).routingState = st.routingState := by
  unfold deleteKeyMetadataState
  split <;> rfl

theorem AccessKeyPermission.withGasBalance_zero (p : AccessKeyPermission) :
    ({ nonce := 0, permission := p.withGasBalance 0 } : AccessKey).gasBalance = 0 := by
  cases p <;> simp [AccessKey.gasBalance, AccessKeyPermission.withGasBalance, AccessKeyPermission.gasKeyInfo?]

theorem AccessKey.gasBalance_of_none (key : AccessKey) (h : key.permission.gasKeyInfo? = none) :
    key.gasBalance = 0 := by
  simp [AccessKey.gasBalance, h]

theorem AccessKey.gasBalance_of_some (key : AccessKey) (balance nonces : Nat)
    (h : key.permission.gasKeyInfo? = some (balance, nonces)) : key.gasBalance = balance := by
  simp [AccessKey.gasBalance, h]

theorem addKeyMetadataState_accountsUnique (c : ReceiptCtx) (st : ChainState) (account : Account)
    (pk : PublicKey) (key : AccessKey) (h : st.AccountsUnique) :
    (addKeyMetadataState c st account pk key).AccountsUnique := by
  unfold addKeyMetadataState
  split
  · exact ChainState.AccountsUnique.congr (ChainState.foldl_setGasKeyNonce_frame _ _ _ _ _).1.symm
      (ChainState.foldl_setGasKeyNonce_frame _ _ _ _ _).2.symm
      (ChainState.accountsUnique_setAccount_new_key h _ _ _ _)
  · exact ChainState.accountsUnique_setAccount_new_key h _ _ _ _

theorem addKeyMetadataState_totalBalance (c : ReceiptCtx) (st : ChainState) (account : Account)
    (pk : PublicKey) (key : AccessKey) (h : st.AccountsUnique)
    (ha : st.account? c.receipt.receiverId = some account) (hk : st.accessKey? c.receipt.receiverId pk = none) :
    (addKeyMetadataState c st account pk key).totalBalance = st.totalBalance := by
  unfold addKeyMetadataState
  split
  · rename_i nonces balance heq
    dsimp only
    rw [ChainState.totalBalance_congr (ChainState.foldl_setGasKeyNonce_frame _ _ _ _ _).1
      (ChainState.foldl_setGasKeyNonce_frame _ _ _ _ _).2]
    rw [ChainState.totalBalance_setAccessKey_new _ _ _ _ (h.setAccount _ _) hk
      (AccessKeyPermission.withGasBalance_zero key.permission)]
    exact ChainState.totalBalance_withStorage st _ account _ h ha
  · rename_i heq
    dsimp only
    rw [ChainState.totalBalance_setAccessKey_new _ _ _ _ (h.setAccount _ _) hk
      (AccessKey.gasBalance_of_none { key with nonce := initialNonce c.ap.blockHeight } heq)]
    exact ChainState.totalBalance_withStorage st _ account _ h ha

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
  · cases ha : before.state.account? c.receipt.receiverId with
    | none => simp [-StateT.run_bind, applyAction, getAccount, getState, hk, ha]
    | some account =>
      cases hg : key.permission.gasKeyInfo? with
      | none =>
        simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, hg,
          addKeyMetadataState, Account.withStorage]
      | some info =>
        obtain ⟨balance, nonces⟩ := info
        simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, hg,
          addKeyMetadataState, Account.withStorage]

theorem applyDeleteKey_run (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (before : Exec) :
    (applyAction c isLast (.deleteKey pk)).run.run before =
      match before.state.accessKey? c.receipt.receiverId pk with
      | none => (.error (.deleteKeyDoesNotExist c.receipt.receiverId pk), before)
      | some key => match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account =>
          if key.gasBalance > maxGasKeyBalanceToBurn then
            (.error (.gasKeyBalanceTooHigh c.receipt.receiverId (some pk) key.gasBalance), before)
          else
            let result := { before with
              state := deleteKeyMetadataState c before.state account pk key
              actionTokensBurnt := before.actionTokensBurnt + key.gasBalance }
            (.ok (), result) := by
  cases hk : before.state.accessKey? c.receipt.receiverId pk with
  | none => simp [-StateT.run_bind, applyAction, getState, hk]
  | some key =>
    cases ha : before.state.account? c.receipt.receiverId with
    | none => simp [-StateT.run_bind, applyAction, getAccount, getState, hk, ha]
    | some account =>
      cases hg : key.permission.gasKeyInfo? with
      | none =>
        have hb := AccessKey.gasBalance_of_none key hg
        simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, hg, hb,
          deleteKeyMetadataState, maxGasKeyBalanceToBurn, Account.withStorage]
      | some info =>
        obtain ⟨balance, nonces⟩ := info
        have hb := AccessKey.gasBalance_of_some key balance nonces hg
        by_cases hmax : balance > maxGasKeyBalanceToBurn
        · simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, hg, hb,
            hmax, deleteKeyMetadataState, Account.withStorage]
        · simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hk, ha, hg, hb,
            hmax, deleteKeyMetadataState, Exec.burnAction, Account.withStorage]

theorem funded_addKey (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (key : AccessKey) :
    (applyAction c isLast (.addKey pk key)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyAddKey_run] at hrun
  split at hrun
  · have hbad := congrArg Prod.fst hrun; cases hbad
  · rename_i hk
    cases ha : before.state.account? c.receipt.receiverId with
    | none =>
      simp only [ha] at hrun
      have hbad := congrArg Prod.fst hrun; cases hbad
    | some account =>
      simp only [ha] at hrun
      apply metadata_return_funded c.cfg c.action.gasPrice before after value _ ?_ ?_ hrun
      · exact addKeyMetadataState_accountsUnique c before.state account pk key hwf
      · apply addKeyMetadataState_totalBalance c before.state account pk key hwf ha
        cases hq : before.state.accessKey? c.receipt.receiverId pk with
        | none => rfl
        | some _ => simp [hq] at hk

theorem deleteKeyMetadataState_accountsUnique (c : ReceiptCtx) (st : ChainState) (account : Account)
    (pk : PublicKey) (key : AccessKey) (h : st.AccountsUnique) :
    (deleteKeyMetadataState c st account pk key).AccountsUnique := by
  unfold deleteKeyMetadataState
  split
  · exact ((h.setAccount _ _).removeAccessKey _ _).removeGasKeyNonces _ _
  · exact (h.setAccount _ _).removeAccessKey _ _

theorem deleteKeyMetadataState_totalBalance (c : ReceiptCtx) (st : ChainState) (account : Account)
    (pk : PublicKey) (key : AccessKey) (h : st.AccountsUnique)
    (ha : st.account? c.receipt.receiverId = some account)
    (hk : st.accessKey? c.receipt.receiverId pk = some key) :
    (deleteKeyMetadataState c st account pk key).totalBalance + key.gasBalance = st.totalBalance := by
  unfold deleteKeyMetadataState
  split
  · dsimp only
    rw [ChainState.totalBalance_removeGasKeyNonces]
    exact ChainState.totalBalance_withStorage_remove st _ pk account _ key h ha hk
  · dsimp only
    exact ChainState.totalBalance_withStorage_remove st _ pk account _ key h ha hk

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
      split at hrun
      · have hbad := congrArg Prod.fst hrun; cases hbad
      · have he := congrArg Prod.snd hrun
        dsimp only at he
        subst after
        refine ⟨deleteKeyMetadataState_accountsUnique c before.state account pk key hwf,
          Exec.FundingStep.of_burn c.cfg c.action.gasPrice key.gasBalance before _ ?_ rfl rfl rfl rfl⟩
        unfold Exec.totalFunds
        have hb := deleteKeyMetadataState_totalBalance c before.state account pk key hwf ha hk
        dsimp only
        omega

end Near
