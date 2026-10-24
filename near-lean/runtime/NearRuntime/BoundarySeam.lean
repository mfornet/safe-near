import NearRuntime.Boundary
import NearRuntime.MaterializeInvariants
import NearRuntime.StateInvariants

/-!
# The boundary is the receipt executor's function call

For a receipt whose only action is a function call, the receipt executor
(`runReceiptActions`) does what the boundary (`execOn`) observes, beyond the
two receipt fees it charges first.
-/

namespace Near.Boundary

open Wasm Wasm.Near
open NearInterface (Context Failure Observation)

theorem ExecM.run_get_bind {α : Type} (k : Exec → ExecM α) (e : Exec) :
    ((get : ExecM Exec) >>= k).run.run e = (k e).run.run e := rfl

theorem ExecM.run_bind {α β : Type} (x : ExecM α) (f : α → ExecM β) (e : Exec) :
    (x >>= f).run.run e =
      match x.run.run e with
      | (.ok a, e') => (f a).run.run e'
      | (.error err, e') => (.error err, e') := by
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases h : StateT.run (ExceptT.run x) e with ⟨_ | a, e'⟩ <;> simp <;> rfl

theorem ExecM.run_modify (f : Exec → Exec) (e : Exec) :
    (modify f : ExecM Unit).run.run e = (.ok (), f e) := rfl

theorem ExecM.run_pure {α : Type} (a : α) (e : Exec) : (pure a : ExecM α).run.run e = (.ok a, e) := rfl

/-- A function call to an existing account passes the admission checks. -/
theorem checkReceiptAction_functionCall_run (c : ReceiptCtx) (onlyAction : Bool) (method : String)
    (args : Bytes) (gas deposit : Nat) (exec : Exec)
    (hacc : (exec.state.account? c.receipt.receiverId).isSome = true) :
    (checkReceiptAction c onlyAction (.functionCall method args gas deposit)).run.run exec =
      (.ok (), exec) := by
  simp only [checkReceiptAction, checkActionAccount, checkActorPermissions, getState, bind_assoc,
    pure_bind]
  rw [ExecM.run_get_bind]
  simp only [hacc, ↓reduceIte]
  rfl

theorem chargeReceiptFee_run (isRefund : Bool) (fee : Nat) (exec : Exec) :
    (chargeReceiptFee isRefund fee).run.run exec =
      (.ok (), { exec with gasBurnt := exec.gasBurnt + fee, gasUsed := exec.gasUsed + fee }) := by
  rfl

/-- A receipt whose only action is a function call: both fees, then the call,
then the storage-stake check. -/
theorem receiptActionBody_functionCall_run (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (seed : Bytes)
    (hact : c.action.actions = [.functionCall method args gas deposit])
    (hseed : actionRandomSeed c 0 = .ok seed) (exec0 : Exec) (account : Account)
    (hacc : exec0.state.account? c.receipt.receiverId = some account) :
    (receiptActionBody c).run.run exec0 =
      let fees := c.cfg.fees.actionFees.newActionReceipt.execution +
        Fees.exec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId
          (.functionCall method args gas deposit)
      let exec1 : Exec :=
        { exec0 with
          gasBurnt := exec0.gasBurnt + fees
          gasUsed := exec0.gasUsed + fees
          failureIndex := some 0 }
      match (applyFunctionCall { c with vmRandomSeed := some seed, vmActionHash := actionHashOf c 0 } method args gas deposit true).run.run exec1 with
      | (.error e, ex) => (.error e, ex)
      | (.ok (), ex) => (checkStorageStake c.cfg c.receipt.receiverId).run.run { ex with failureIndex := none } := by
  simp only [receiptActionBody, hact, runReceiptActionList, List.length_singleton, beq_self_eq_true,
    List.isEmpty_nil, runReceiptActionAt, hseed, runReceiptAction, applyAction, bind_pure_unit,
    bind_assoc]
  simp only [ExecM.run_bind, chargeReceiptFee_run, ExecM.run_modify]
  simp (disch := simp [hacc]) only [checkReceiptAction_functionCall_run]
  simp only [Nat.add_assoc]
  split <;> rename_i heq <;> simp only [heq]

-- TODO(proof): adapt the cloned proof
theorem actionOfPromise_error {codeOf : Bytes → ContractCode} {action : PromiseAction}
    {e : RuntimeError} (h : actionOfPromise codeOf action = .error e) :
    ∃ issue, e = .executionIssue issue := by
  sorry

/-- The first unconvertible action of one receipt. -/
theorem mapM_actionOfPromise (codeOf : Bytes → ContractCode) (actions : List PromiseAction) :
    (match actions.mapM (actionOfPromise codeOf) with
      | .ok _ => none
      | .error (.executionIssue issue) => some issue
      | .error error => some (.interpreterError (repr error).pretty)) =
    actions.findSome? (actionIssue? codeOf) := by
  induction actions with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.mapM_cons, List.findSome?_cons]
    cases ha : actionOfPromise codeOf a with
    | error e =>
      obtain ⟨issue, rfl⟩ := actionOfPromise_error ha
      simp [actionIssue?, ha, bind, Except.bind]
    | ok act =>
      simp only [actionIssue?, ha, bind, Except.bind]
      rw [← ih]
      cases List.mapM (actionOfPromise codeOf) rest <;> rfl

theorem mapM_actionOfPromise_error {codeOf : Bytes → ContractCode} {actions : List PromiseAction}
    {e : RuntimeError} (h : actions.mapM (actionOfPromise codeOf) = .error e) :
    ∃ issue, e = .executionIssue issue := by
  induction actions with
  | nil => simp [List.mapM_nil, pure, Except.pure] at h
  | cons a rest ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases ha : actionOfPromise codeOf a with
    | error e' => rw [ha] at h; cases h; exact actionOfPromise_error ha
    | ok act =>
      rw [ha] at h
      dsimp only at h
      cases hr : List.mapM (actionOfPromise codeOf) rest with
      | error e' => rw [hr] at h; cases h; exact ih hr
      | ok acts => rw [hr] at h; cases h

/-- The runtime's validation of promised actions fails exactly where the
boundary's `actionsIssue?` finds an issue, with that issue. -/
theorem validateFunctionCallActions_issue (c : ReceiptCtx) (outcome : VMOutcome) :
    (match validateFunctionCallActions c outcome with
      | .ok _ => none
      | .error (.executionIssue issue) => some issue
      | .error error => some (.interpreterError (repr error).pretty)) =
    actionsIssue? c.codeOf outcome.receipts := by
  unfold validateFunctionCallActions actionsIssue?
  generalize outcome.receipts = specs
  induction specs with
  | nil => rfl
  | cons spec rest ih =>
    have hs := mapM_actionOfPromise c.codeOf spec.actions
    rw [List.findSome?_cons, List.forIn_cons]
    cases hm : spec.actions.mapM (actionOfPromise c.codeOf) with
    | error e =>
      obtain ⟨issue, rfl⟩ := mapM_actionOfPromise_error hm
      rw [hm] at hs
      simp only at hs
      rw [← hs]
      rfl
    | ok acts =>
      rw [hm] at hs
      simp only at hs
      rw [← hs]
      simp only [bind, Except.bind, pure, Except.pure]
      exact ih

theorem validateFunctionCallActions_error {c : ReceiptCtx} {outcome : VMOutcome} {e : RuntimeError}
    (h : validateFunctionCallActions c outcome = .error e) : ∃ issue, e = .executionIssue issue := by
  unfold validateFunctionCallActions at h
  generalize outcome.receipts = specs at h
  induction specs with
  | nil => cases h
  | cons spec rest ih =>
    rw [List.forIn_cons] at h
    cases hm : spec.actions.mapM (actionOfPromise c.codeOf) with
    | error e' =>
      rw [hm] at h
      cases h
      exact mapM_actionOfPromise_error hm
    | ok acts =>
      rw [hm] at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      exact ih h

theorem checkStorageStake_run (cfg : RuntimeConfig) (id : AccountId) (exec : Exec) (a : Account)
    (hacc : exec.state.account? id = some a) :
    (checkStorageStake cfg id).run.run exec =
      if storageStakeDeficit cfg a > 0 then (.error (.lackBalanceForState id (storageStakeDeficit cfg a)), exec)
      else (.ok (), exec) := by
  simp only [checkStorageStake, getState, bind_assoc, pure_bind]
  rw [ExecM.run_get_bind]
  simp only [hacc]
  split <;> rfl

theorem contractStorage_setContractStorage_self (st : ChainState) (id : AccountId)
    (s : List (Bytes × Bytes)) : (st.setContractStorage id s).contractStorage id = s := by
  simp [ChainState.setContractStorage, ChainState.contractStorage, Assoc.lookup_insert_self]

/-! ## The seam -/

/-- A boundary context that is the receipt's: the receipt's accounts, the
action's arguments, gas and deposit, the account's resources, the block, the
action's random seed and the chunk trie. -/
structure Corresponds (c : ReceiptCtx) (seed : Bytes) (account : Account) (method : String)
    (args : Bytes) (gas deposit : Nat) (trie : TrieOverlay.State) (ctx : Context) : Prop where
  current : ctx.current.val = c.receipt.receiverId
  signer : ctx.signer.val = c.action.signerId
  signerPk : ctx.signerPk = c.action.signerPublicKey
  predecessor : ctx.predecessor.val = c.receipt.predecessorId
  args : ctx.args = args
  results : ctx.promiseResults = c.promiseResults
  height : ctx.blockHeight = c.ap.blockHeight
  timestamp : ctx.timestamp = c.ap.blockTimestamp
  epoch : ctx.epochHeight = c.ap.epochHeight
  balance : ctx.balance = account.amount
  locked : ctx.locked = account.locked
  usage : ctx.storageUsage = account.storageUsage
  deposit : ctx.attached = deposit
  gas : ctx.prepaidGas = gas
  seed : ctx.randomSeed = seed
  trie : ctx.trie = trie
  outputs : ctx.outputDataReceivers.map Subtype.val = c.action.outputDataReceivers.map (·.receiverId)
  protocol : ctx.protocol = c.cfg
  method : ctx.method = method
  actionHash : ctx.actionHash = (actionHashOf c 0).getD []
  yields : ctx.existingYields = c.vmYields
  chain : ctx.chainId = bytesOfString c.ap.chainId

theorem Corresponds.vmContext {c : ReceiptCtx} {seed : Bytes} {account : Account} {method : String}
    {args : Bytes} {gas deposit : Nat} {trie : TrieOverlay.State} {ctx : Context}
    (h : Corresponds c seed account method args gas deposit trie ctx) :
    functionCallContext { c with vmRandomSeed := some seed, vmActionHash := actionHashOf c 0 } account args gas deposit true (some trie) =
      toVMContext ctx :=
  functionCallContext_eq_toVMContext _ account args gas deposit true trie ctx h.current h.signer
    h.signerPk h.predecessor h.args h.results h.height h.timestamp h.epoch h.balance h.locked h.usage
    h.deposit h.gas h.seed h.trie (by simpa using h.outputs) h.actionHash h.yields h.chain

/-- The boundary's reading of a receipt failure. -/
def runtimeFailure : RuntimeError → Failure
  | .functionCallError error => failureOf error
  | .executionIssue issue => .executionIssue issue.message
  | .lackBalanceForState _ deficit => .lackBalanceForState deficit
  | error => .other (repr error).pretty

theorem account?_withoutIds (st : ChainState) (id : AccountId) :
    st.withoutIds.account? id = st.account? id := rfl

theorem contractStorage_withoutIds (st : ChainState) (id : AccountId) :
    st.withoutIds.contractStorage id = st.contractStorage id := rfl

/-- **The seam.** For a receipt whose only action is a function call to an
account with code, the receipt executor does what the boundary observes,
beyond the receipt and action fees it charges first: the same logs and burnt
gas; on success the same storage, balance, usage, used gas and trie; on
failure the same failure, with the account rolled back. -/
-- TODO(proof): adapt the cloned proof
theorem functionCallReceipt_seam (c : ReceiptCtx) (method : String) (args : Bytes)
    (gas deposit : Nat) (seed : Bytes)
    (hact : c.action.actions = [.functionCall method args gas deposit])
    (hseed : actionRandomSeed c 0 = .ok seed) (st0 : ChainState) (account : Account)
    (code : ContractCode) (trie : TrieOverlay.State) (ctx : Context)
    (hacc : st0.account? c.receipt.receiverId = some account) (hcode : account.code = some code)
    (hissue : code.decodeIssue = none) (htrie : c.ap.storageAccounting = some trie)
    (hcor : Corresponds c seed account method args gas deposit trie ctx) :
    let r := execOn ⟨code, c.codeOf⟩ (st0.contractStorage c.receipt.receiverId) ctx
    let fees := c.cfg.fees.actionFees.newActionReceipt.execution +
      Fees.exec c.cfg.fees.actionFees c.cfg.wasm.ethImplicitAccounts c.receipt.receiverId
        (.functionCall method args gas deposit)
    let res := runReceiptActions c st0
    res.1.logs = r.logs ∧ res.1.gasBurnt = fees + r.burntGas ∧
    ((∃ d, r.outcome = .ok d) →
      res.2 = none ∧
      res.1.gasUsed = fees + r.usedGas + (run c.cfg code.module code.size method (toVMContext ctx)
        (st0.contractStorage c.receipt.receiverId)).distributedGas ∧
      (res.1.state.contractStorage c.receipt.receiverId).toFinset = r.storage ∧
      (res.1.state.account? c.receipt.receiverId).map (·.amount) = some r.balance ∧
      (res.1.state.account? c.receipt.receiverId).map (·.storageUsage) = some r.storageUsage ∧
      res.1.storageAccounting.getD ctx.trie = r.trie) ∧
    (∀ f, r.outcome = .error f →
      ∃ re, res.2 = some re ∧ runtimeFailure re = f ∧
        (rollbackReceipt st0 res.1 res.2).state = st0 ∧
        (rollbackReceipt st0 res.1 res.2).storageAccounting.getD { ctx.trie with prospective := [] } =
          r.trie) := by
  sorry

end Near.Boundary
