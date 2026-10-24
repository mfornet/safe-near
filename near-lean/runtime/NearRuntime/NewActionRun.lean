import NearRuntime.Apply

namespace Near
open Wasm.Near

/-! Executable unfoldings of the global-contract, gas-key and delegate actions, and the fields
they leave alone. -/

/-! ### Running the state monad of an action -/

@[simp] theorem exec_id_pure (value : α) : (pure value : Id α) = value := rfl

@[simp] theorem execM_run_bind (operation : ExecM α) (next : α → ExecM β) (before : Exec) :
    (operation >>= next).run.run before =
      (match operation.run.run before with
        | (result, middle) => match result with
          | .ok value => (next value).run.run middle
          | .error error => (.error error, middle) : Except RuntimeError β × Exec) := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  cases he : operation.run.run before with
  | mk result middle => cases result <;> rfl

@[simp] theorem execM_run_get (before : Exec) : (get : ExecM Exec).run.run before = (.ok before, before) := rfl
@[simp] theorem execM_run_modify (f : Exec → Exec) (before : Exec) :
    (modify f : ExecM Unit).run.run before = (.ok (), f before) := rfl
@[simp] theorem execM_run_pure (value : α) (before : Exec) :
    (pure value : ExecM α).run.run before = (.ok value, before) := rfl
@[simp] theorem execM_run_throw (error : RuntimeError) (before : Exec) :
    (throw error : ExecM α).run.run before = (.error error, before) := rfl


/-- The routing, allocator and yield fields of a state: ledger-level updates (accounts, keys,
nonces, global contracts) never touch them. -/
def ChainState.routingState (st : ChainState) :=
  (st.postponed, st.pendingDataCount, st.postponedByData, st.receivedData, st.delayed, st.nextId,
   st.yieldIndices, st.yieldTimeouts, st.yieldReceipts, st.yieldStatus)

theorem ChainState.nextId_of_routing {a b : ChainState} (h : a.routingState = b.routingState) :
    a.nextId = b.nextId := by
  unfold ChainState.routingState at h
  simp only [Prod.mk.injEq] at h
  exact h.2.2.2.2.2.1

theorem ChainState.postponed_of_routing {a b : ChainState} (h : a.routingState = b.routingState) :
    a.postponed = b.postponed := by
  unfold ChainState.routingState at h
  simp only [Prod.mk.injEq] at h
  exact h.1

theorem ChainState.delayed_of_routing {a b : ChainState} (h : a.routingState = b.routingState) :
    a.delayed = b.delayed := by
  unfold ChainState.routingState at h
  simp only [Prod.mk.injEq] at h
  exact h.2.2.2.2.1

/-- Same routing and yield maps; the allocator may have advanced. -/
def ChainState.RoutingAdvance (a b : ChainState) : Prop :=
  b.postponed = a.postponed ∧ b.pendingDataCount = a.pendingDataCount ∧
    b.postponedByData = a.postponedByData ∧ b.receivedData = a.receivedData ∧ b.delayed = a.delayed ∧
    b.yieldIndices = a.yieldIndices ∧ b.yieldTimeouts = a.yieldTimeouts ∧ b.yieldReceipts = a.yieldReceipts ∧
    b.yieldStatus = a.yieldStatus ∧ a.nextId ≤ b.nextId

theorem ChainState.RoutingAdvance.nextId_le {a b : ChainState} (h : a.RoutingAdvance b) : a.nextId ≤ b.nextId :=
  h.2.2.2.2.2.2.2.2.2

theorem ChainState.RoutingAdvance.refl (st : ChainState) : st.RoutingAdvance st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem ChainState.RoutingAdvance.trans {a b c : ChainState} (h1 : a.RoutingAdvance b) (h2 : b.RoutingAdvance c) :
    a.RoutingAdvance c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2.2.2⟩

theorem ChainState.RoutingAdvance.of_routing {a b : ChainState} (h : b.routingState = a.routingState) :
    a.RoutingAdvance b := by
  unfold ChainState.routingState at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h7, h8, h9, h10, Nat.le_of_eq h6.symm⟩

theorem ChainState.RoutingAdvance.freshId (st : ChainState) : st.RoutingAdvance st.freshId.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_succ _⟩

theorem ChainState.setGlobalNonceIf_routing (st : ChainState) (enabled : Bool) (id : Wasm.GlobalContractId)
    (nonce : Nat) : (st.setGlobalNonceIf enabled id nonce).routingState = st.routingState := by
  unfold ChainState.setGlobalNonceIf
  split <;> rfl

/-- The account after it starts using a global contract. -/
def Account.usingGlobal (account : Account) (contract : Wasm.GlobalContractId) : Account :=
  { account with
    code := none
    global := some contract
    versionTwo := true
    storageUsage := (account.storageUsage - account.contractStorageUsage) + contract.length }

theorem applyUseGlobalContract_run (c : ReceiptCtx) (isLast : Bool) (contract : Wasm.GlobalContractId)
    (before : Exec) :
    (applyAction c isLast (.useGlobalContract contract)).run.run before =
      match before.state.globalCodeOf? contract with
      | none => (.error (.globalContractDoesNotExist contract), before)
      | some _ =>
        match before.state.account? c.receipt.receiverId with
        | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
        | some account =>
          (.ok (), { before with state := before.state.setAccount c.receipt.receiverId (account.usingGlobal contract) }) := by
  cases hg : before.state.globalCodeOf? contract with
  | none => simp [-StateT.run_bind, applyAction, getState, hg]
  | some code =>
    cases ha : before.state.account? c.receipt.receiverId with
    | none => simp [-StateT.run_bind, applyAction, getAccount, getState, hg, ha]
    | some account =>
      simp [-StateT.run_bind, applyAction, getAccount, getState, putAccount, modifyState, hg, ha, Account.usingGlobal]

theorem gasKeyDeposit_routing {st moved : ChainState} {id : AccountId} {pk : PublicKey} {deposit : Nat}
    (h : gasKeyDeposit st id pk deposit = .ok moved) : moved.routingState = st.routingState := by
  unfold gasKeyDeposit at h
  cases hg : gasKeyOf st id pk with
  | error e => simp [hg, bind, Except.bind] at h
  | ok triple =>
    simp only [hg, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst moved; rfl

theorem gasKeyWithdrawal_routing {st moved : ChainState} {id : AccountId} {pk : PublicKey} {amount : Nat}
    (h : gasKeyWithdrawal st id pk amount = .ok moved) : moved.routingState = st.routingState := by
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
        subst moved; rfl

theorem delegateKeyUpdate_routing (st : ChainState) (sender : AccountId) (pk : PublicKey) (lane : Option Nat)
    (nonce : Nat) : (delegateKeyUpdate st sender pk lane nonce).routingState = st.routingState := by
  unfold delegateKeyUpdate
  cases lane with
  | none => dsimp only; split <;> rfl
  | some index => rfl

theorem delegateKeyState_routing {c : ReceiptCtx} {st st' : ChainState} {sender : AccountId} {pk : PublicKey}
    {nonce : Nat} {nonceIndex : Option Nat} {inner : List Action} {receiver : AccountId}
    (h : delegateKeyState c st sender pk nonce nonceIndex inner receiver = .ok st') :
    st'.routingState = st.routingState := by
  unfold delegateKeyState at h
  cases hl : delegateKeyCheck c st sender pk nonce nonceIndex inner receiver with
  | error e => simp [hl] at h
  | ok lane =>
    simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst st'
    exact delegateKeyUpdate_routing _ _ _ _ _

theorem delegateState_routing {c : ReceiptCtx} {st moved : ChainState} {act : Action}
    (h : delegateState c st act = .ok moved) : moved.routingState = st.routingState := by
  unfold delegateState at h
  split at h
  · exact delegateKeyState_routing h
  · cases h; rfl

theorem applyTransferToGasKey_run (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (deposit : Nat)
    (before : Exec) :
    (applyAction c isLast (.transferToGasKey pk deposit)).run.run before =
      match gasKeyDeposit before.state c.receipt.receiverId pk deposit with
      | .error e => (.error e, before)
      | .ok moved => (.ok (), { before with state := moved }) := by
  cases h : gasKeyDeposit before.state c.receipt.receiverId pk deposit <;>
    simp [-StateT.run_bind, applyAction, liftExcept, getState, modifyState, h]

theorem applyWithdrawFromGasKey_run (c : ReceiptCtx) (isLast : Bool) (pk : PublicKey) (amount : Nat)
    (before : Exec) :
    (applyAction c isLast (.withdrawFromGasKey pk amount)).run.run before =
      match gasKeyWithdrawal before.state c.receipt.receiverId pk amount with
      | .error e => (.error e, before)
      | .ok moved => (.ok (), { before with state := moved }) := by
  cases h : gasKeyWithdrawal before.state c.receipt.receiverId pk amount <;>
    simp [-StateT.run_bind, applyAction, liftExcept, getState, modifyState, h]

/-- The state after the deployment's account and nonce updates, before the receipt id is drawn. -/
def deployGlobalMoved (c : ReceiptCtx) (before : Exec) (plan : DeployGlobalPlan) : ChainState :=
  (before.state.setAccount c.receipt.receiverId plan.account).setGlobalNonceIf
    c.cfg.globalContractDistributionNonce plan.identifier plan.nonce

theorem deployGlobalMoved_routing (c : ReceiptCtx) (before : Exec) (plan : DeployGlobalPlan) :
    (deployGlobalMoved c before plan).routingState = before.state.routingState :=
  ChainState.setGlobalNonceIf_routing _ _ _ _

/-- The execution after a global contract deployment was planned: the storage cost is burnt, the
distribution nonce moves and a distribution receipt is emitted. -/
def deployGlobalResult (c : ReceiptCtx) (before : Exec) (plan : DeployGlobalPlan) (code : ContractCode) : Exec :=
  let burnt := before.burnAction plan.burn
  let moved := deployGlobalMoved c before plan
  { burnt with
    state := moved.freshId.2
    newReceipts := burnt.newReceipts ++ [{
      predecessorId := c.receipt.receiverId
      receiverId := systemReceiver
      receiptId := moved.freshId.1
      receipt := .globalDistribution {
        id := plan.identifier, targetShard := c.ap.shardId, code, nonce := plan.nonce } }] }

theorem applyDeployGlobalContract_run (c : ReceiptCtx) (isLast : Bool) (code : ContractCode)
    (mode : GlobalDeployMode) (before : Exec) :
    (applyAction c isLast (.deployGlobalContract code mode)).run.run before =
      match before.state.account? c.receipt.receiverId with
      | none => (.error (.accountDoesNotExist c.receipt.receiverId), before)
      | some account =>
        match planDeployGlobal c before.state account code mode with
        | .error e => (.error e, before)
        | .ok plan => (.ok (), deployGlobalResult c before plan code) := by
  cases ha : before.state.account? c.receipt.receiverId with
  | none => simp [-StateT.run_bind, applyAction, applyDeployGlobalContract, getAccount, getState, ha]
  | some account =>
    cases hp : planDeployGlobal c before.state account code mode with
    | error e =>
      simp [-StateT.run_bind, applyAction, applyDeployGlobalContract, getAccount, getState, liftExcept, ha, hp]
    | ok plan =>
      simp [-StateT.run_bind, applyAction, applyDeployGlobalContract, getAccount, getState, liftExcept, putAccount,
        modifyState, emit, fresh, ha, hp, deployGlobalResult, Exec.burnAction]
      rfl

/-- The execution after a delegate action's checks and key update passed: the inner receipt's
execution gas is reserved, its send fees are burnt and the receipt is emitted. -/
def delegateResult (c : ReceiptCtx) (before : Exec) (act : Action) (moved : ChainState) : Exec :=
  let send := Fees.prepaidSend c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts act
  { before with
    state := moved.freshId.2
    gasBurnt := before.gasBurnt + send
    gasUsed := before.gasUsed + delegateRequired c act + send
    newReceipts := before.newReceipts ++ [delegateReceipt c act moved.freshId.1] }

theorem applyDelegateAction_run (c : ReceiptCtx) (act : Action) (before : Exec) :
    (applyDelegateAction c act).run.run before =
      match delegateChecks c act with
      | .error e => (.error e, before)
      | .ok () =>
        match delegateState c before.state act with
        | .error e => (.error e, before)
        | .ok moved => (.ok (), delegateResult c before act moved) := by
  cases hc : delegateChecks c act with
  | error e => simp [-StateT.run_bind, applyDelegateAction, liftExcept, hc]
  | ok u =>
    cases u
    cases hs : delegateState c before.state act with
    | error e => simp [-StateT.run_bind, applyDelegateAction, liftExcept, getState, hc, hs]
    | ok moved =>
      simp [-StateT.run_bind, applyDelegateAction, liftExcept, getState, modifyState, useGas, burnGas, emit, fresh,
        hc, hs, delegateResult]
      rfl

/-! ### Yield timeouts -/

/-- The yield-timeout stage changes only the timeout queue, its indices and the allocator. -/
def ChainState.TimeoutStep (before after : ChainState) : Prop :=
  ∃ indices timeouts n, before.nextId ≤ n ∧
    after = { before with yieldIndices := indices, yieldTimeouts := timeouts, nextId := n }

theorem ChainState.TimeoutStep.refl (st : ChainState) : st.TimeoutStep st :=
  ⟨st.yieldIndices, st.yieldTimeouts, st.nextId, Nat.le_refl _, rfl⟩

theorem ChainState.TimeoutStep.nextId_le {a b : ChainState} (h : a.TimeoutStep b) : a.nextId ≤ b.nextId := by
  obtain ⟨_, _, n, hn, rfl⟩ := h
  exact hn

theorem ChainState.TimeoutStep.accounts {a b : ChainState} (h : a.TimeoutStep b) : b.accounts = a.accounts := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.accessKeys {a b : ChainState} (h : a.TimeoutStep b) : b.accessKeys = a.accessKeys := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.postponed {a b : ChainState} (h : a.TimeoutStep b) : b.postponed = a.postponed := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.pendingDataCount {a b : ChainState} (h : a.TimeoutStep b) :
    b.pendingDataCount = a.pendingDataCount := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.postponedByData {a b : ChainState} (h : a.TimeoutStep b) :
    b.postponedByData = a.postponedByData := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.receivedData {a b : ChainState} (h : a.TimeoutStep b) :
    b.receivedData = a.receivedData := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.delayed {a b : ChainState} (h : a.TimeoutStep b) : b.delayed = a.delayed := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.yieldReceipts {a b : ChainState} (h : a.TimeoutStep b) :
    b.yieldReceipts = a.yieldReceipts := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl
theorem ChainState.TimeoutStep.yieldStatus {a b : ChainState} (h : a.TimeoutStep b) :
    b.yieldStatus = a.yieldStatus := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem ChainState.TimeoutStep.trans {a b c : ChainState} (h1 : a.TimeoutStep b) (h2 : b.TimeoutStep c) :
    a.TimeoutStep c := by
  obtain ⟨i1, t1, n1, hn1, rfl⟩ := h1
  obtain ⟨i2, t2, n2, hn2, rfl⟩ := h2
  exact ⟨i2, t2, n2, Nat.le_trans hn1 hn2, rfl⟩

/-- The receipt a timed-out yield sends to its own account. -/
def Receipt.IsTimeoutResume (r : Receipt) : Prop :=
  ∃ dataId, r.predecessorId = r.receiverId ∧
    r.receipt = .data { dataId := 0, data := none, resumeDataId := some dataId }

/-- What the timeout stage guarantees about its result: the receipts it adds are timeout resumes with
distinct ids from the allocator interval it consumed. -/
def TimeoutSpec (st : ChainState) (receipts : List Receipt)
    (r : ChainState × List Receipt × List ReceiptIdentityBirth) : Prop :=
  st.TimeoutStep r.1 ∧ ∃ new, r.2.1 = receipts ++ new ∧ (new.map (·.receiptId)).Nodup ∧
    ∀ x ∈ new, x.IsTimeoutResume ∧ st.nextId ≤ x.receiptId ∧ x.receiptId < r.1.nextId

theorem TimeoutSpec.rest {st st' : ChainState} {receipts : List Receipt} (resume : Receipt)
    {r : ChainState × List Receipt × List ReceiptIdentityBirth}
    (hstep : st.TimeoutStep st') (hresume : resume.IsTimeoutResume)
    (hid : st.nextId ≤ resume.receiptId ∧ resume.receiptId < st'.nextId)
    (h : TimeoutSpec st' (receipts ++ [resume]) r) : TimeoutSpec st receipts r := by
  obtain ⟨hs, new, hnew, hnodup, hmem⟩ := h
  refine ⟨hstep.trans hs, resume :: new, by simpa using hnew, ?_, ?_⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnodup⟩
    intro hin
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hin
    have h1 := (hmem x hx).2.1
    have h2 := hid.2
    have h3 : x.receiptId = resume.receiptId := hxe
    rw [h3] at h1
    exact Nat.not_le_of_lt h2 h1
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hresume, hid.1, Nat.lt_of_lt_of_le hid.2 hs.nextId_le⟩
    · obtain ⟨h1, h2, h3⟩ := hmem x hx
      exact ⟨h1, Nat.le_trans hstep.nextId_le h2, h3⟩

theorem TimeoutSpec.skip {st st' : ChainState} {receipts : List Receipt}
    {r : ChainState × List Receipt × List ReceiptIdentityBirth}
    (hstep : st.TimeoutStep st') (h : TimeoutSpec st' receipts r) : TimeoutSpec st receipts r := by
  obtain ⟨hs, new, hnew, hnodup, hmem⟩ := h
  refine ⟨hstep.trans hs, new, hnew, hnodup, ?_⟩
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hmem x hx
  exact ⟨h1, Nat.le_trans hstep.nextId_le h2, h3⟩

theorem TimeoutSpec.refl (st : ChainState) (receipts : List Receipt) (births : List ReceiptIdentityBirth) :
    TimeoutSpec st receipts (st, receipts, births) :=
  ⟨ChainState.TimeoutStep.refl st, [], by simp, by simp, by simp⟩

theorem resolveYieldTimeouts_spec (ap : ApplyState) (limit : Option Nat) (used : Nat) (fuel : Nat) :
    ∀ (st : ChainState) (receipts : List Receipt) (births : List ReceiptIdentityBirth),
      TimeoutSpec st receipts (resolveYieldTimeouts ap limit used fuel (st, receipts, births)) := by
  induction fuel with
  | zero =>
    intro st receipts births
    exact TimeoutSpec.refl st receipts births
  | succ fuel ih =>
    intro st receipts births
    unfold resolveYieldTimeouts
    split
    · exact TimeoutSpec.refl st receipts births
    · rename_i first next _
      split
      · split
        · exact TimeoutSpec.refl st receipts births
        · rename_i entry _
          split
          · exact TimeoutSpec.refl st receipts births
          · dsimp only
            split
            · refine TimeoutSpec.rest _ ?_ ?_ ?_ (ih _ _ _)
              · exact ⟨_, _, st.nextId + 1, Nat.le_succ _, rfl⟩
              · exact ⟨entry.dataId, rfl, rfl⟩
              · exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
            · refine TimeoutSpec.skip ?_ (ih _ _ _)
              exact ⟨_, _, st.nextId, Nat.le_refl _, rfl⟩
      · exact TimeoutSpec.refl st receipts births

end Near
