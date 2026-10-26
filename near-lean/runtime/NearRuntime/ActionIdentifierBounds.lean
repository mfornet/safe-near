import NearRuntime.RoutingIdentifierBounds
import NearRuntime.FinalizeStages

namespace Near
open Wasm.Near


theorem resumeReceipts_nextId_le (account : AccountId) (resumes : List (Bytes × Bytes))
    (initial : ChainState) (receipts : List Receipt) :
    initial.nextId ≤ (resumeReceipts account resumes initial receipts).1.nextId := by
  unfold resumeReceipts
  suffices ∀ (items : List (Bytes × Bytes)) (acc : ChainState × List Receipt),
      acc.1.nextId ≤ (items.foldl (fun (acc : ChainState × List Receipt) resume =>
        (acc.1.freshId.2, acc.2 ++ [{
          predecessorId := account
          receiverId := account
          receiptId := acc.1.freshId.1
          receipt := .data { dataId := 0, data := some resume.2, resumeDataId := some resume.1 } }]))
        acc).1.nextId from this resumes (initial, receipts)
  intro items
  induction items with
  | nil => intro acc; exact Nat.le_refl _
  | cons item rest ih =>
    intro acc
    rw [List.foldl_cons]
    exact (Nat.le_add_right acc.1.nextId 1).trans (ih (acc.1.freshId.2, _))

theorem yieldBookkeeping_nextId (c : ReceiptCtx) (outcome : VMOutcome) (initial : ChainState) :
    (yieldBookkeeping c outcome initial).nextId = initial.nextId := by
  unfold yieldBookkeeping
  dsimp only
  have h1 := foldl_frame (fun st : ChainState => st.nextId) (fun (st : ChainState) dataId =>
    { st with
      yieldTimeouts := st.yieldTimeouts ++ [((initial.yieldIndices.getD (0, 0)).2 +
        ((outcome.receipts.filterMap (·.yieldDataId)).idxOf dataId),
        { account := c.receipt.receiverId, dataId, expiresAt := c.ap.blockHeight + c.cfg.wasm.limits.yieldTimeoutLengthInBlocks })]
      yieldStatus := Assoc.insert st.yieldStatus (c.receipt.receiverId, dataId) .yielded })
    (by intros; rfl) (outcome.receipts.filterMap (·.yieldDataId)) initial
  have h2 := foldl_frame (fun st : ChainState => st.nextId) (fun (st : ChainState) resume =>
    { st with yieldStatus := Assoc.insert st.yieldStatus (c.receipt.receiverId, resume.1) .resumeInitiated })
    (by intros; rfl) outcome.resumes
    ((outcome.receipts.filterMap (·.yieldDataId)).foldl (fun (st : ChainState) dataId =>
    { st with
      yieldTimeouts := st.yieldTimeouts ++ [((initial.yieldIndices.getD (0, 0)).2 +
        ((outcome.receipts.filterMap (·.yieldDataId)).idxOf dataId),
        { account := c.receipt.receiverId, dataId, expiresAt := c.ap.blockHeight + c.cfg.wasm.limits.yieldTimeoutLengthInBlocks })]
      yieldStatus := Assoc.insert st.yieldStatus (c.receipt.receiverId, dataId) .yielded }) initial)
  split
  · exact h2.trans h1
  · exact h2.trans h1

theorem functionCallYields_nextId_mono (c : ReceiptCtx) (outcome : VMOutcome) (effects : FunctionCallEffects) :
    effects.state.nextId ≤ (functionCallYields c outcome effects).state.nextId := by
  unfold functionCallYields
  dsimp only
  rw [yieldBookkeeping_nextId]
  exact resumeReceipts_nextId_le _ _ _ _

theorem functionCallYields_idsBelowNext (c : ReceiptCtx) (outcome : VMOutcome) (effects : FunctionCallEffects)
    (h : effects.state.IdsBelowNext) : (functionCallYields c outcome effects).state.IdsBelowNext := by
  apply h.of_frame
  · have hf := congrArg ChainState.liveIds (functionCallYields_frame c outcome effects)
    exact hf
  · exact functionCallYields_nextId_mono c outcome effects

theorem commitFunctionCall_idsBelowNext (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects)
    (h : exec.state.IdsBelowNext) :
    (exec.commitFunctionCall outcome effects).state.IdsBelowNext := by
  rw [show (exec.commitFunctionCall outcome effects).state = effects.state from rfl]
  rw [functionCallEffects_success c account outcome isLast exec.state effects heffects]
  exact functionCallYields_idsBelowNext _ _ _ (materializeFunctionCall_idsBelowNext c isLast outcome _ h)

theorem refundAllowance_idsBelowNext (st : ChainState) (receiver : AccountId) (pk : PublicKey) (amount : Nat)
    (h : st.IdsBelowNext) : (st.refundAllowance receiver pk amount).IdsBelowNext := by
  unfold ChainState.refundAllowance
  split
  · exact h
  · split <;> exact h

theorem transferCreditState_idsBelowNext (c : ReceiptCtx) (st : ChainState) (account : Account) (amount : Nat)
    (h : st.IdsBelowNext) : (transferCreditState c st account amount).IdsBelowNext := by
  unfold transferCreditState
  split
  · exact refundAllowance_idsBelowNext _ _ _ _ h
  · exact h

theorem ChainState.IdsBelowNext.of_advance {st moved : ChainState} (h : st.IdsBelowNext)
    (hr : st.RoutingAdvance moved) : moved.IdsBelowNext := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, h8, _, h10⟩ := hr
  intro id hm
  have hm' : id ∈ st.liveIds := by
    simp only [ChainState.liveIds, h1, h2, h3, h4, h5, h8] at hm ⊢
    exact hm
  have := h id hm'
  omega

theorem ChainState.IdsBelowNext.of_routing {st moved : ChainState} (h : st.IdsBelowNext)
    (hr : moved.routingState = st.routingState) : moved.IdsBelowNext :=
  h.of_advance (ChainState.RoutingAdvance.of_routing hr)

/-- Every raw action preserves the allocator bound, on failures as well as
successes. Account changes do not alter routing references. -/
theorem applyAction_idsBelowNext (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (h : before.state.IdsBelowNext) : ((applyAction c isLast action).run.run before).2.state.IdsBelowNext := by
  cases action with
  | createAccount => rw [applyCreateAccount_run]; repeat' (first | exact h | split)
  | deployContract code => rw [applyDeployContract_run]; repeat' (first | exact h | split)
  | functionCall method args gas deposit =>
    rw [show applyAction c isLast (.functionCall method args gas deposit) =
      applyFunctionCall c method args gas deposit isLast from rfl, applyFunctionCall_run]
    cases ha : before.state.account? c.receipt.receiverId with
    | none => exact h
    | some account =>
      dsimp only
      cases hc : resolveContract before.state account with
      | none => exact h
      | some code =>
        dsimp only
        cases hi : code.decodeIssue with
        | some issue => exact h
        | none =>
          dsimp only
          generalize ho : run c.cfg code.module code.size method
            (functionCallContext c account args gas deposit isLast before.storageAccounting)
            (before.state.contractStorage c.receipt.receiverId) = outcome
          cases he : outcome.aborted with
          | some error => exact h
          | none =>
            dsimp only
            cases hf : functionCallEffects c account outcome isLast before.state with
            | error error => exact h
            | ok effects =>
              exact commitFunctionCall_idsBelowNext (before.recordVMOutcome outcome) c account outcome isLast effects hf h
  | transfer amount =>
    rw [applyTransfer_run]
    split
    · exact transferCreditState_idsBelowNext _ _ _ _ h
    · split
      · exact h
      · exact h
      · split <;> exact h
  | stake amount pk =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-StateT.run_bind, applyAction, getAccount, getState, ha]
    repeat' (first | exact h | split)
  | addKey pk key =>
    rw [applyAddKey_run]
    repeat' (first | exact h | exact h.of_routing (addKeyMetadataState_routing _ _ _ _ _) | split)
  | deleteKey pk =>
    rw [applyDeleteKey_run]
    repeat' (first | exact h | exact h.of_routing (deleteKeyMetadataState_routing _ _ _ _ _) | split)
  | useGlobalContract contract => rw [applyUseGlobalContract_run]; repeat' (first | exact h | split)
  | deployGlobalContract code mode =>
    rw [applyDeployGlobalContract_run]
    repeat' (first | exact h | exact h.of_advance ((ChainState.RoutingAdvance.of_routing (deployGlobalMoved_routing c _ _)).trans (ChainState.RoutingAdvance.freshId _)) | split)
  | transferToGasKey pk deposit =>
    rw [applyTransferToGasKey_run]
    repeat' (first | exact h | exact ChainState.IdsBelowNext.of_routing h (gasKeyDeposit_routing (by assumption)) | split)
  | withdrawFromGasKey pk amount =>
    rw [applyWithdrawFromGasKey_run]
    repeat' (first | exact h | exact ChainState.IdsBelowNext.of_routing h (gasKeyWithdrawal_routing (by assumption)) | split)
  | delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2 =>
    change ((applyDelegateAction c _).run.run before).2.state.IdsBelowNext
    rw [applyDelegateAction_run]
    repeat' (first | exact h | exact h.of_advance ((ChainState.RoutingAdvance.of_routing (delegateState_routing (by assumption))).trans (ChainState.RoutingAdvance.freshId _)) | split)
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    repeat' (first | exact h | exact h.freshId | exact h.of_advance (deleteAccountFundedResult_advance _ _ _ _) | split)

/-- The invariant is required after failures as well as successes, so it can
compose through arbitrary action sequences before receipt rollback. -/
def ExecM.PreservesIdBounds (operation : ExecM α) : Prop :=
  ∀ before, before.state.IdsBelowNext → (operation.run.run before).2.state.IdsBelowNext

theorem ExecM.PreservesIdBounds.bind {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.PreservesIdBounds) (hnext : ∀ value, (next value).PreservesIdBounds) :
    (operation >>= next).PreservesIdBounds := by
  intro before hmissing
  rw [execM_run_bind]
  have hp := hfirst before hmissing
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp
    cases result with
    | error error => exact hp
    | ok value => exact hnext value middle hp

theorem idBounds_pure (value : α) : (pure value : ExecM α).PreservesIdBounds := by intro before h; exact h

theorem idBounds_throw (error : RuntimeError) : (throw error : ExecM α).PreservesIdBounds := by intro before h; exact h

theorem idBounds_get : (get : ExecM Exec).PreservesIdBounds := by intro before h; exact h

theorem idBounds_getState : getState.PreservesIdBounds := by intro before h; exact h

theorem idBounds_fee (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).PreservesIdBounds := by
  intro before h
  unfold chargeReceiptFee burnGas
  exact h

theorem idBounds_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).PreservesIdBounds := by
  unfold checkReceiptAction
  refine ExecM.PreservesIdBounds.bind idBounds_getState (fun st => ?_)
  split
  · exact idBounds_throw _
  · refine ExecM.PreservesIdBounds.bind idBounds_get (fun before => ?_)
    split
    · exact idBounds_throw _
    · exact idBounds_pure _

theorem idBounds_checkStorageStake (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).PreservesIdBounds := by
  unfold checkStorageStake
  refine ExecM.PreservesIdBounds.bind idBounds_getState (fun st => ?_)
  split
  · dsimp only
    split
    · exact idBounds_throw _
    · exact idBounds_pure _
  · exact idBounds_pure _

theorem idBounds_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).PreservesIdBounds := by
  unfold runReceiptAction
  exact (idBounds_fee _ _).bind (fun _ => (idBounds_checkReceiptAction _ _ _).bind
    (fun _ => applyAction_idsBelowNext _ _ _))

theorem idBounds_runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool)
    (action : Action) (index : Nat) : (runReceiptActionAt c onlyAction isLast action index).PreservesIdBounds := by
  unfold runReceiptActionAt
  split
  · cases hs : actionRandomSeed c index with
    | error error =>
      exact idBounds_throw _
    | ok seed =>
      exact idBounds_runReceiptAction _ _ _ _
  · exact idBounds_runReceiptAction _ _ _ _

theorem idBounds_failureIndex (index : Option Nat) :
    (modify fun e => { e with failureIndex := index } : ExecM Unit).PreservesIdBounds := by
  intro before h
  exact h

theorem idBounds_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action)
    (index : Nat) : (runReceiptActionList c onlyAction actions index).PreservesIdBounds := by
  induction actions generalizing index with
  | nil => exact idBounds_pure _
  | cons action rest ih =>
    exact (idBounds_failureIndex (some index)).bind (fun _ =>
      (idBounds_runReceiptActionAt c onlyAction rest.isEmpty action index).bind (fun _ => ih (index + 1)))

theorem idBounds_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).PreservesIdBounds := by
  unfold receiptActionBody
  exact (idBounds_fee _ _).bind (fun _ => (idBounds_runReceiptActionList _ _ _ _).bind
    (fun _ => (idBounds_failureIndex none).bind (fun _ => idBounds_checkStorageStake _ _)))

theorem runReceiptActions_idsBelowNext (c : ReceiptCtx) (st : ChainState) (h : st.IdsBelowNext) :
    (runReceiptActions c st).1.state.IdsBelowNext := by
  have hp := idBounds_receiptActionBody c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } h
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he] using hp


theorem Exec.addBalanceRefund_idsBelowNext (exec : Exec) (receiver : AccountId) (amount : Nat)
    (h : exec.state.IdsBelowNext) : (exec.addBalanceRefund receiver amount).state.IdsBelowNext := h.freshId

theorem Exec.addGasRefund_idsBelowNext (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat)
    (h : exec.state.IdsBelowNext) : (exec.addGasRefund receiver pk amount).state.IdsBelowNext := h.freshId

theorem Exec.addFailureData_idsBelowNext (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (h : exec.state.IdsBelowNext) : (exec.addFailureData receiver outputs).state.IdsBelowNext := by
  unfold Exec.addFailureData
  dsimp only
  apply foldl_preserves (fun pair : ChainState × List Receipt => pair.1.IdsBelowNext)
  · intro pair item hp
    exact hp.freshId
  · exact h

theorem Exec.addSuccessData_idsBelowNext (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver) (bytes : Bytes)
    (h : exec.state.IdsBelowNext) : (exec.addSuccessData receiver outputs bytes).state.IdsBelowNext := by
  unfold Exec.addSuccessData
  dsimp only
  apply foldl_preserves (fun pair : ChainState × List Receipt => pair.1.IdsBelowNext)
  · intro pair item hp
    exact hp.freshId
  · exact h

theorem Exec.deliverResult_idsBelowNext (exec : Exec) (receiver : AccountId) (outputs : List DataReceiver)
    (h : exec.state.IdsBelowNext) : (exec.deliverResult receiver outputs).state.IdsBelowNext := by
  unfold Exec.deliverResult
  split
  · exact Exec.addSuccessData_idsBelowNext _ _ _ _ h
  · exact Exec.addFailureData_idsBelowNext _ _ _ h
  · exact h

theorem Exec.finishReceiptResult_idsBelowNext (exec : Exec) (c : ReceiptCtx) (failed : Option RuntimeError)
    (h : exec.state.IdsBelowNext) : (exec.finishReceiptResult c failed).state.IdsBelowNext := by
  unfold Exec.finishReceiptResult
  apply Exec.deliverResult_idsBelowNext
  split <;> exact h

theorem Exec.creditReceiptReward_idsBelowNext (exec : Exec) (cfg : RuntimeConfig) (receiver : AccountId)
    (burnPrice purchasePrice : Nat) (h : exec.state.IdsBelowNext) :
    (exec.creditReceiptReward cfg receiver burnPrice purchasePrice).state.IdsBelowNext := by
  unfold Exec.creditReceiptReward
  split <;> exact h

/-- Finalization may allocate refunds and failure envelopes; none of these
operations changes old routing references or moves the counter backwards. -/
theorem finalizeReceipt_idsBelowNext (c : ReceiptCtx) (st : ChainState) (raw : Exec) (failed : Option RuntimeError)
    (hinitial : st.IdsBelowNext) (hraw : raw.state.IdsBelowNext) :
    (finalizeReceipt c st raw failed).state.IdsBelowNext := by
  refine finalizeReceipt_stages (fun e => e.state.IdsBelowNext) c st raw failed ?_
    (fun _ _ _ h => h)
    (fun e _ _ h => Exec.addBalanceRefund_idsBelowNext e _ _ h)
    (fun e _ _ _ h => Exec.addGasRefund_idsBelowNext e _ _ _ h)
    (fun e _ _ h => Exec.creditReceiptReward_idsBelowNext e _ _ _ _ h)
    (fun e h => Exec.finishReceiptResult_idsBelowNext e c failed h)
    (fun _ _ _ h => h)
  cases failed <;> first | exact hraw | exact hinitial

theorem applyActionReceipt_idsBelowNext (c : ReceiptCtx) (st : ChainState) (h : st.IdsBelowNext) :
    (applyActionReceipt c st).state.IdsBelowNext :=
  finalizeReceipt_idsBelowNext c st _ _ h (runReceiptActions_idsBelowNext c st h)

end Near
