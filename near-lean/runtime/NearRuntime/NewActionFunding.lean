import NearRuntime.BalanceActionFunding
import NearRuntime.NewActionRun

namespace Near
open Wasm.Near

/-! Funding rules of the global-contract, gas-key and delegate actions. -/

/-! Executable unfoldings and funding rules of the global-contract, gas-key and delegate actions. -/

theorem AccessKeyPermission.gasKeyInfo?_withGasBalance (p : AccessKeyPermission) (balance moved nonces : Nat)
    (hp : p.gasKeyInfo? = some (balance, nonces)) :
    (p.withGasBalance moved).gasKeyInfo? = some (moved, nonces) := by
  cases p <;> simp_all [AccessKeyPermission.withGasBalance, AccessKeyPermission.gasKeyInfo?]

theorem AccessKey.gasBalance_of_info (key : AccessKey) (balance nonces : Nat)
    (hp : key.permission.gasKeyInfo? = some (balance, nonces)) : key.gasBalance = balance := by
  simp [AccessKey.gasBalance, hp]

theorem AccessKey.gasBalance_withGasBalance (key : AccessKey) (balance moved nonces : Nat)
    (hp : key.permission.gasKeyInfo? = some (balance, nonces)) :
    ({ key with permission := key.permission.withGasBalance moved } : AccessKey).gasBalance = moved := by
  simp [AccessKey.gasBalance, AccessKeyPermission.gasKeyInfo?_withGasBalance _ _ _ _ hp]

/-- Replacing a key moves exactly the difference of the gas balances. -/
theorem ChainState.totalBalance_setAccessKey_change (st : ChainState) (id : AccountId) (pk : PublicKey)
    (k key : AccessKey) (h : st.AccountsUnique) (hk : st.accessKey? id pk = some key) :
    (st.setAccessKey id pk k).totalBalance + key.gasBalance = st.totalBalance + k.gasBalance := by
  have hg := ChainState.gasKeyFunds_setAccessKey st id pk k h.accessKeys
  rw [hk] at hg
  simp only [Option.map_some, Option.getD_some] at hg
  unfold ChainState.totalBalance
  have hacc : (st.setAccessKey id pk k).accounts = st.accounts := rfl
  rw [hacc]
  omega

/-! ### UseGlobalContract -/

theorem funded_useGlobalContract (c : ReceiptCtx) (isLast : Bool) (contract : Wasm.GlobalContractId) :
    (applyAction c isLast (.useGlobalContract contract)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyUseGlobalContract_run] at hrun
  cases hg : before.state.globalCodeOf? contract with
  | none => simp only [hg] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
  | some code =>
    simp only [hg] at hrun
    cases ha : before.state.account? c.receipt.receiverId with
    | none => simp only [ha] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
    | some account =>
      simp only [ha] at hrun
      refine metadata_return_funded c.cfg c.action.gasPrice before after value _ (hwf.setAccount _ _) ?_ hrun
      exact ChainState.totalBalance_metadata _ _ account _ hwf ha rfl rfl

/-! ### Gas key deposits and withdrawals -/

theorem gasKeyOf_some {st : ChainState} {id : AccountId} {pk : PublicKey} {key : AccessKey} {balance nonces : Nat}
    (h : gasKeyOf st id pk = .ok (key, balance, nonces)) :
    (st.account? id).isSome = true ∧ st.accessKey? id pk = some key ∧ key.permission.gasKeyInfo? = some (balance, nonces) := by
  unfold gasKeyOf at h
  cases hA : st.account? id with
  | none => simp [hA] at h
  | some a =>
    simp only [hA, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at h
    cases hk : st.accessKey? id pk with
    | none => simp [hk] at h
    | some k =>
      cases hi : k.permission.gasKeyInfo? with
      | none => simp [hk, hi] at h
      | some info =>
        obtain ⟨b, n⟩ := info
        simp [hk, hi] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl, hi⟩

theorem gasKeyDeposit_account_isSome {st moved : ChainState} {id : AccountId} {pk : PublicKey} {deposit : Nat}
    (h : gasKeyDeposit st id pk deposit = .ok moved) : (st.account? id).isSome = true := by
  unfold gasKeyDeposit at h
  cases hg : gasKeyOf st id pk with
  | error e => simp [hg, bind, Except.bind] at h
  | ok triple => exact (gasKeyOf_some hg).1

theorem gasKeyDeposit_ok {st moved : ChainState} {id : AccountId} {pk : PublicKey} {deposit : Nat}
    (h : gasKeyDeposit st id pk deposit = .ok moved) (hwf : st.AccountsUnique) :
    moved.AccountsUnique ∧ moved.totalBalance = st.totalBalance + deposit := by
  unfold gasKeyDeposit at h
  cases hg : gasKeyOf st id pk with
  | error e => simp [hg, bind, Except.bind] at h
  | ok triple =>
    obtain ⟨key, balance, nonces⟩ := triple
    obtain ⟨_, hk, hi⟩ := gasKeyOf_some hg
    simp only [hg, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst moved
    refine ⟨hwf.setAccessKey _ _ _ (ChainState.account_of_accessKey hwf _ _ _ hk), ?_⟩
    have hc := ChainState.totalBalance_setAccessKey_change st id pk
      { key with permission := key.permission.withGasBalance (balance + deposit) } key hwf hk
    rw [AccessKey.gasBalance_withGasBalance key balance _ nonces hi, AccessKey.gasBalance_of_info key balance nonces hi] at hc
    omega

theorem gasKeyWithdrawal_ok {st moved : ChainState} {id : AccountId} {pk : PublicKey} {amount : Nat}
    (h : gasKeyWithdrawal st id pk amount = .ok moved) (hwf : st.AccountsUnique) :
    moved.AccountsUnique ∧ moved.totalBalance = st.totalBalance := by
  unfold gasKeyWithdrawal at h
  cases hg : gasKeyOf st id pk with
  | error e => simp [hg, bind, Except.bind] at h
  | ok triple =>
    obtain ⟨key, balance, nonces⟩ := triple
    obtain ⟨_, hk, hi⟩ := gasKeyOf_some hg
    simp only [hg, bind, Except.bind] at h
    by_cases hb : balance < amount
    · simp [hb] at h
    · simp only [hb, ite_false] at h
      have haccount := ChainState.account_of_accessKey hwf id pk key hk
      cases hA : st.account? id with
      | none => rw [hA] at haccount; simp at haccount
      | some a =>
        have h1 : (st.setAccessKey id pk
            { key with permission := key.permission.withGasBalance (balance - amount) }).account? id = some a := hA
        simp only [h1, pure, Except.pure, Except.ok.injEq] at h
        subst moved
        have hwf1 := hwf.setAccessKey id pk { key with permission := key.permission.withGasBalance (balance - amount) }
          haccount
        refine ⟨hwf1.setAccount _ _, ?_⟩
        have hc := ChainState.totalBalance_setAccessKey_change st id pk
          { key with permission := key.permission.withGasBalance (balance - amount) } key hwf hk
        rw [AccessKey.gasBalance_withGasBalance key balance _ nonces hi,
          AccessKey.gasBalance_of_info key balance nonces hi] at hc
        have ha := ChainState.totalBalance_setAccount (st.setAccessKey id pk
          { key with permission := key.permission.withGasBalance (balance - amount) }) id
          { a with amount := a.amount + amount } a hwf1 h1
        simp only at ha
        omega

theorem funded_transferToGasKey (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (deposit : Nat) :
    (applyAction c isLast (.transferToGasKey pk deposit)).Funded c.cfg c.action.gasPrice deposit := by
  intro before after value hwf hrun
  rw [applyTransferToGasKey_run] at hrun
  cases h : gasKeyDeposit before.state c.receipt.receiverId pk deposit with
  | error e => simp only [h] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
  | ok moved =>
    simp only [h] at hrun
    obtain ⟨hu, hb⟩ := gasKeyDeposit_ok h hwf
    refine balance_return_funded c.cfg c.action.gasPrice deposit before after { before with state := moved } value hu ?_ rfl rfl rfl hrun
    change moved.totalBalance + receiptsFunds c.cfg before.newReceipts =
      before.state.totalBalance + receiptsFunds c.cfg before.newReceipts + deposit
    omega

theorem funded_withdrawFromGasKey (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (amount : Nat) :
    (applyAction c isLast (.withdrawFromGasKey pk amount)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyWithdrawFromGasKey_run] at hrun
  cases h : gasKeyWithdrawal before.state c.receipt.receiverId pk amount with
  | error e => simp only [h] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
  | ok moved =>
    simp only [h] at hrun
    obtain ⟨hu, hb⟩ := gasKeyWithdrawal_ok h hwf
    refine metadata_return_funded c.cfg c.action.gasPrice before after value _ hu hb hrun

/-! ### DeployGlobalContract -/

theorem planDeployGlobal_ok {c : ReceiptCtx} {st : ChainState} {account : Account} {code : ContractCode}
    {mode : GlobalDeployMode} {plan : DeployGlobalPlan} (h : planDeployGlobal c st account code mode = .ok plan) :
    plan.account.amount + plan.burn = account.amount ∧ plan.account.locked = account.locked := by
  unfold planDeployGlobal at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | contradiction
    | (cases h; dsimp only; exact ⟨by omega, rfl⟩)

theorem ChainState.setGlobalNonceIf_frame (st : ChainState) (enabled : Bool) (id : Wasm.GlobalContractId)
    (nonce : Nat) : (st.setGlobalNonceIf enabled id nonce).accounts = st.accounts ∧
      (st.setGlobalNonceIf enabled id nonce).accessKeys = st.accessKeys := by
  unfold ChainState.setGlobalNonceIf
  split <;> exact ⟨rfl, rfl⟩

theorem funded_deployGlobalContract (c : ReceiptCtx) (isLast : Bool) (code : ContractCode)
    (mode : GlobalDeployMode) :
    (applyAction c isLast (.deployGlobalContract code mode)).Funded c.cfg c.action.gasPrice 0 := by
  intro before after value hwf hrun
  rw [applyDeployGlobalContract_run] at hrun
  cases ha : before.state.account? c.receipt.receiverId with
  | none => simp only [ha] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
  | some account =>
    simp only [ha] at hrun
    cases hp : planDeployGlobal c before.state account code mode with
    | error e => simp only [hp] at hrun; have hbad := congrArg Prod.fst hrun; cases hbad
    | ok plan =>
      simp only [hp] at hrun
      have he := congrArg Prod.snd hrun
      dsimp only at he
      subst after
      obtain ⟨hamt, hlock⟩ := planDeployGlobal_ok hp
      have hset := hwf.setAccount c.receipt.receiverId plan.account
      have hframe := ChainState.setGlobalNonceIf_frame (before.state.setAccount c.receipt.receiverId plan.account)
        c.cfg.globalContractDistributionNonce plan.identifier plan.nonce
      refine ⟨(hset.congr hframe.1.symm hframe.2.symm).congr rfl rfl, ?_⟩
      have hbal := ChainState.totalBalance_setAccount before.state c.receipt.receiverId plan.account account hwf ha
      have hbal' : (deployGlobalMoved c before plan).freshId.2.totalBalance =
          (before.state.setAccount c.receipt.receiverId plan.account).totalBalance :=
        ChainState.totalBalance_congr hframe.1 hframe.2
      refine Exec.FundingStep.of_burn c.cfg c.action.gasPrice plan.burn before _ ?_ rfl rfl rfl rfl
      unfold Exec.totalFunds deployGlobalResult
      simp only [receiptsFunds, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, Fees.receiptFunds, Exec.burnAction, hbal']
      omega

/-! ### Delegate -/

theorem prepaidExecList_eq_sum (f : ActionFees) (ethEnabled : Bool) (receiver : AccountId) (l : List Action) :
    Fees.prepaidExecList f ethEnabled receiver l = (l.map (Fees.prepaidExec f ethEnabled receiver)).sum := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [Fees.prepaidExecList, ih]

theorem depositList_eq_totalDeposit (l : List Action) : Action.depositList l = Fees.totalDeposit l := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [Action.depositList, Fees.totalDeposit, ih]

theorem totalPrepaidSend_eq_zero (f : ActionFees) (ethEnabled : Bool) (l : List Action)
    (h : l.any Action.isDelegate = false) : Fees.totalPrepaidSend f ethEnabled l = 0 := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have ha : Fees.prepaidSend f ethEnabled a = 0 := by
      cases a <;> first | rfl | (simp [Action.isDelegate] at h)
    have hrest := ih h.2
    simp only [Fees.totalPrepaidSend, List.map_cons, List.sum_cons, ha, Nat.zero_add]
    exact hrest

theorem delegateChecks_inner {c : ReceiptCtx} {sender receiver : AccountId} {inner : List Action}
    {nonce : Nat} {nonceIndex : Option Nat} {maxBlockHeight : Nat} {pk : PublicKey} {signature : Bytes} {v2 : Bool}
    (h : delegateChecks c (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2) = .ok ()) :
    inner.any Action.isDelegate = false ∧ sender = c.receipt.receiverId := by
  unfold delegateChecks at h
  by_cases hi : inner.any Action.isDelegate = true
  · simp [hi] at h
  · have hi' : inner.any Action.isDelegate = false := by simpa using hi
    simp only [hi', Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨hi', ?_⟩
    by_cases hv : (!c.ap.verifyDelegate (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2)) = true
    · simp [hv] at h
    · by_cases he : c.ap.blockHeight > maxBlockHeight
      · simp [hv, he] at h
      · by_cases hs : (sender != c.receipt.receiverId) = true
        · simp [hv, he, hs] at h
        · simpa using hs

theorem delegate_budget (c : ReceiptCtx) (sender receiver : AccountId) (inner : List Action)
    (nonce : Nat) (nonceIndex : Option Nat) (maxBlockHeight : Nat) (pk : PublicKey) (signature : Bytes) (v2 : Bool)
    (h : inner.any Action.isDelegate = false) :
    Fees.receiptGasBudget c.cfg receiver inner =
      delegateRequired c (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2) := by
  simp only [delegateRequired]
  unfold Fees.receiptGasBudget
  rw [totalPrepaidSend_eq_zero _ _ _ h, prepaidExecList_eq_sum]
  omega

theorem delegateKeyUpdate_ok (st : ChainState) (sender : AccountId) (pk : PublicKey) (lane : Option Nat)
    (nonce : Nat) (hwf : st.AccountsUnique) :
    (delegateKeyUpdate st sender pk lane nonce).AccountsUnique ∧
      (delegateKeyUpdate st sender pk lane nonce).totalBalance = st.totalBalance := by
  unfold delegateKeyUpdate
  cases lane with
  | none =>
    dsimp only
    cases hk : st.accessKey? sender pk with
    | none => exact ⟨hwf, rfl⟩
    | some key =>
      exact ⟨hwf.setAccessKey _ _ _ (ChainState.account_of_accessKey hwf _ _ _ hk),
        ChainState.totalBalance_setAccessKey_same st sender pk _ key hwf hk rfl⟩
  | some index => exact ⟨hwf, ChainState.totalBalance_congr rfl rfl⟩

theorem delegateKeyState_ok {c : ReceiptCtx} {st st' : ChainState} {sender : AccountId} {pk : PublicKey}
    {nonce : Nat} {nonceIndex : Option Nat} {inner : List Action} {receiver : AccountId}
    (h : delegateKeyState c st sender pk nonce nonceIndex inner receiver = .ok st') (hwf : st.AccountsUnique) :
    st'.AccountsUnique ∧ st'.totalBalance = st.totalBalance := by
  unfold delegateKeyState at h
  cases hl : delegateKeyCheck c st sender pk nonce nonceIndex inner receiver with
  | error e => simp [hl] at h
  | ok lane =>
    simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst st'
    exact delegateKeyUpdate_ok st sender pk lane nonce hwf

theorem delegateState_ok {c : ReceiptCtx} {st moved : ChainState} {act : Action}
    (h : delegateState c st act = .ok moved) (hwf : st.AccountsUnique) :
    moved.AccountsUnique ∧ moved.totalBalance = st.totalBalance := by
  unfold delegateState at h
  split at h
  · exact delegateKeyState_ok h hwf
  · cases h; exact ⟨hwf, rfl⟩

theorem funded_delegate (c : ReceiptCtx) (isLast : Bool) (sender receiver : AccountId) (inner : List Action)
    (nonce : Nat) (nonceIndex : Option Nat) (maxBlockHeight : Nat) (pk : PublicKey) (signature : Bytes) (v2 : Bool)
    (hreceiver : c.receipt.receiverId ≠ systemAccount) :
    (applyAction c isLast (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2)).Funded
      c.cfg c.action.gasPrice (Action.depositList inner) := by
  intro before after value hwf hrun
  have hrun' : (applyDelegateAction c
      (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2)).run.run before =
        (.ok value, after) := hrun
  rw [applyDelegateAction_run] at hrun'
  cases hc : delegateChecks c
      (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2) with
  | error e => simp only [hc] at hrun'; have hbad := congrArg Prod.fst hrun'; cases hbad
  | ok u =>
    cases u
    obtain ⟨hno, hsender⟩ := delegateChecks_inner hc
    simp only [hc] at hrun'
    cases hs : delegateState c before.state
        (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2) with
    | error e => simp only [hs] at hrun'; have hbad := congrArg Prod.fst hrun'; cases hbad
    | ok moved =>
      simp only [hs] at hrun'
      have he := congrArg Prod.snd hrun'
      dsimp only at he
      subst after
      obtain ⟨hu, hb⟩ := delegateState_ok hs hwf
      have hbudget := delegate_budget c sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2 hno
      have hnotrefund : (sender == systemAccount) = false := by
        rw [hsender]; simpa using hreceiver
      refine ⟨hu.congr rfl rfl, ?_⟩
      unfold Exec.FundingStep Exec.totalFunds delegateResult
      have hfresh : moved.freshId.2.totalBalance = before.state.totalBalance := by
        rw [← hb]; exact ChainState.totalBalance_congr rfl rfl
      simp only [receiptsFunds, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, Fees.receiptFunds, delegateReceipt, Receipt.isRefund, hnotrefund,
        depositList_eq_totalDeposit, hbudget, hfresh]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_mul]
      omega

/-! ### Account frames -/

theorem gasKeyDeposit_account {st moved : ChainState} {id : AccountId} {pk : PublicKey} {deposit : Nat}
    (h : gasKeyDeposit st id pk deposit = .ok moved) (x : AccountId) : moved.account? x = st.account? x := by
  unfold gasKeyDeposit at h
  cases hg : gasKeyOf st id pk with
  | error e => simp [hg, bind, Except.bind] at h
  | ok triple =>
    simp only [hg, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst moved; rfl

/-- A withdrawal needs the account it credits, and touches no other. -/
theorem gasKeyWithdrawal_account {st moved : ChainState} {id : AccountId} {pk : PublicKey} {amount : Nat}
    (h : gasKeyWithdrawal st id pk amount = .ok moved) :
    (st.account? id).isSome = true ∧ ∀ x, id ≠ x → moved.account? x = st.account? x := by
  unfold gasKeyWithdrawal at h
  cases hg : gasKeyOf st id pk with
  | error e => simp [hg, bind, Except.bind] at h
  | ok triple =>
    obtain ⟨key, balance, nonces⟩ := triple
    simp only [hg, bind, Except.bind] at h
    by_cases hb : balance < amount
    · simp [hb] at h
    · simp only [hb, ite_false] at h
      cases hA : (st.setAccessKey id pk
          { key with permission := key.permission.withGasBalance (balance - amount) }).account? id with
      | none => simp [hA] at h
      | some a =>
        simp only [hA, pure, Except.pure, Except.ok.injEq] at h
        subst moved
        refine ⟨by rw [show st.account? id = some a from hA]; rfl, ?_⟩
        intro x hne
        exact ChainState.account?_setAccount_ne _ _ _ _ hne

theorem delegateKeyUpdate_account (st : ChainState) (sender : AccountId) (pk : PublicKey) (lane : Option Nat)
    (nonce : Nat) (x : AccountId) : (delegateKeyUpdate st sender pk lane nonce).account? x = st.account? x := by
  unfold delegateKeyUpdate
  cases lane with
  | none => dsimp only; split <;> rfl
  | some index => rfl

theorem delegateKeyState_account {c : ReceiptCtx} {st st' : ChainState} {sender : AccountId} {pk : PublicKey}
    {nonce : Nat} {nonceIndex : Option Nat} {inner : List Action} {receiver : AccountId}
    (h : delegateKeyState c st sender pk nonce nonceIndex inner receiver = .ok st') (x : AccountId) :
    st'.account? x = st.account? x := by
  unfold delegateKeyState at h
  cases hl : delegateKeyCheck c st sender pk nonce nonceIndex inner receiver with
  | error e => simp [hl] at h
  | ok lane =>
    simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst st'
    exact delegateKeyUpdate_account _ _ _ _ _ _

theorem delegateState_account {c : ReceiptCtx} {st moved : ChainState} {act : Action}
    (h : delegateState c st act = .ok moved) (x : AccountId) : moved.account? x = st.account? x := by
  unfold delegateState at h
  split at h
  · exact delegateKeyState_account h x
  · cases h; rfl

theorem deployGlobalResult_account_ne (c : ReceiptCtx) (before : Exec) (plan : DeployGlobalPlan)
    (code : ContractCode) (x : AccountId) (hne : c.receipt.receiverId ≠ x) :
    (deployGlobalResult c before plan code).state.account? x = before.state.account? x := by
  have hf := ChainState.setGlobalNonceIf_frame (before.state.setAccount c.receipt.receiverId plan.account)
    c.cfg.globalContractDistributionNonce plan.identifier plan.nonce
  change Assoc.lookup (deployGlobalMoved c before plan).accounts x = _
  unfold deployGlobalMoved
  rw [hf.1]
  exact ChainState.account?_setAccount_ne _ _ _ _ hne

theorem delegateResult_account (c : ReceiptCtx) (before : Exec) (act : Action) (moved : ChainState)
    (x : AccountId) : (delegateResult c before act moved).state.account? x = moved.account? x := rfl

theorem delegateKeyCheck_account {c : ReceiptCtx} {st : ChainState} {sender : AccountId} {pk : PublicKey}
    {nonce : Nat} {nonceIndex : Option Nat} {inner : List Action} {receiver : AccountId} {lane : Option Nat}
    (h : delegateKeyCheck c st sender pk nonce nonceIndex inner receiver = .ok lane) :
    (st.account? sender).isSome = true := by
  unfold delegateKeyCheck at h
  cases hA : st.account? sender with
  | none => simp [hA, bind, Except.bind] at h
  | some a => rfl

theorem delegateState_account_isSome {c : ReceiptCtx} {st moved : ChainState}
    {sender receiver : AccountId} {inner : List Action} {nonce : Nat} {nonceIndex : Option Nat}
    {maxBlockHeight : Nat} {pk : PublicKey} {signature : Bytes} {v2 : Bool}
    (h : delegateState c st (.delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2) =
      .ok moved) : (st.account? sender).isSome = true := by
  unfold delegateState delegateKeyState at h
  cases hl : delegateKeyCheck c st sender pk nonce nonceIndex inner receiver with
  | error e => simp [hl] at h
  | ok lane => exact delegateKeyCheck_account hl

end Near
