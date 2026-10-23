import NearRuntime.BlockAllocatorMonotonicity

namespace Near
open Wasm.Near

/-- Every identity or dependency reference in the execution's emitted receipts
has already been allocated by its current state. -/
def Exec.OutputIdsBelowNext (exec : Exec) : Prop :=
  ∀ receipt ∈ exec.newReceipts, ∀ id ∈ receipt.liveIds, id < exec.state.nextId

def ReceiptCtx.CallbackIdsBelow (c : ReceiptCtx) (bound : Nat) : Prop :=
  ∀ output ∈ c.action.outputDataReceivers, output.dataId < bound

theorem Exec.OutputIdsBelowNext.of_frame {before after : Exec} (h : before.OutputIdsBelowNext)
    (hreceipts : after.newReceipts = before.newReceipts) (hnext : before.state.nextId ≤ after.state.nextId) :
    after.OutputIdsBelowNext := by
  intro receipt hm id hid
  exact (h receipt (hreceipts ▸ hm) id hid).trans_le hnext

theorem Exec.addBalanceRefund_outputIds (exec : Exec) (receiver : AccountId) (amount : Nat)
    (h : exec.OutputIdsBelowNext) : (exec.addBalanceRefund receiver amount).OutputIdsBelowNext := by
  intro receipt hm id hid
  simp only [Exec.addBalanceRefund, refundReceipt, ChainState.freshId, List.mem_append, List.mem_singleton] at hm
  rcases hm with hold | rfl
  · exact (h receipt hold id hid).trans (Nat.lt_succ_self _)
  · simp [Receipt.liveIds] at hid
    subst id
    exact Nat.lt_succ_self _

theorem Exec.addGasRefund_outputIds (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount : Nat)
    (h : exec.OutputIdsBelowNext) : (exec.addGasRefund receiver pk amount).OutputIdsBelowNext := by
  intro receipt hm id hid
  simp only [Exec.addGasRefund, gasRefundReceipt, ChainState.freshId, List.mem_append, List.mem_singleton] at hm
  rcases hm with hold | rfl
  · exact (h receipt hold id hid).trans (Nat.lt_succ_self _)
  · simp [Receipt.liveIds] at hid
    subst id
    exact Nat.lt_succ_self _

/-- VM emission extends the already bounded output list and advances the shared
counter. Inherited callback references are transported from the current context. -/
theorem commitFunctionCall_outputIds (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects) (h : exec.OutputIdsBelowNext)
    (hcallbacks : c.CallbackIdsBelow exec.state.nextId) :
    (exec.commitFunctionCall outcome effects).OutputIdsBelowNext := by
  have heffects' := functionCallEffects_success c account outcome isLast exec.state effects heffects
  let initial := (exec.state.setAccount c.receipt.receiverId
    { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
      c.receipt.receiverId outcome.storage
  have he := materializeFunctionCall_liveIds_below c isLast outcome initial hcallbacks
  have hn := commitFunctionCall_nextId_mono exec c account outcome isLast effects heffects
  rw [heffects'] at hn
  intro receipt hm id hid
  change receipt ∈ exec.newReceipts ++ effects.receipts at hm
  rw [heffects'] at hm
  change id < effects.state.nextId
  rw [heffects']
  rcases List.mem_append.mp hm with hold | hnew
  · exact (h receipt hold id hid).trans_le hn
  · exact he receipt hnew id hid

/-- Output bounds survive raw actions on both success and failure. -/
theorem applyAction_outputIds (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (h : before.OutputIdsBelowNext) (hcallbacks : c.CallbackIdsBelow before.state.nextId) :
    ((applyAction c isLast action).run.run before).2.OutputIdsBelowNext := by
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
      cases hc : account.code with
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
              exact commitFunctionCall_outputIds (before.recordVMOutcome outcome) c account outcome isLast effects hf h hcallbacks
  | transfer amount =>
    rw [applyTransfer_run]
    split
    · rename_i account haccount
      apply Exec.OutputIdsBelowNext.of_frame (after := { before with state := transferCreditState c before.state account amount }) h rfl
      exact Nat.le_of_eq (transferCreditState_nextId _ _ _ _).symm
    · split
      · exact h
      · split <;> exact h
  | stake amount pk =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-StateT.run_bind, applyAction, getAccount, getState, ha]
    repeat' (first | exact h | split)
  | addKey pk key => rw [applyAddKey_run]; repeat' (first | exact h | split)
  | deleteKey pk => rw [applyDeleteKey_run]; repeat' (first | exact h | split)
  | useGlobalContract _ => exact h
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · exact Exec.addBalanceRefund_outputIds before beneficiary _ h

/-- The callback bound is required at entry, while monotonicity transports it
between successive operations. -/
def ExecM.BoundsOutputIds (c : ReceiptCtx) (operation : ExecM α) : Prop :=
  ∀ before, c.CallbackIdsBelow before.state.nextId → before.OutputIdsBelowNext →
    (operation.run.run before).2.OutputIdsBelowNext

theorem ExecM.BoundsOutputIds.bind {c : ReceiptCtx} {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.BoundsOutputIds c) (hmono : operation.NextIdMonotone)
    (hnext : ∀ value, (next value).BoundsOutputIds c) : (operation >>= next).BoundsOutputIds c := by
  intro before hcallbacks hbefore
  rw [execM_run_bind]
  have hp := hfirst before hcallbacks hbefore
  have hn := hmono before
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp hn
    cases result with
    | error error => exact hp
    | ok value =>
      exact hnext value middle (fun output hm => (hcallbacks output hm).trans_le hn) hp

theorem outputIds_pure (c : ReceiptCtx) (value : α) : (pure value : ExecM α).BoundsOutputIds c := by
  intro before _ h; exact h

theorem outputIds_throw (c : ReceiptCtx) (error : RuntimeError) : (throw error : ExecM α).BoundsOutputIds c := by
  intro before _ h; exact h

theorem outputIds_get (c : ReceiptCtx) : (get : ExecM Exec).BoundsOutputIds c := by intro before _ h; exact h

theorem outputIds_getState (c : ReceiptCtx) : getState.BoundsOutputIds c := by intro before _ h; exact h

theorem outputIds_fee (c : ReceiptCtx) (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).BoundsOutputIds c := by
  intro before _ h
  unfold chargeReceiptFee burnGas
  exact h

theorem outputIds_checkReceiptAction (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).BoundsOutputIds c := by
  unfold checkReceiptAction
  refine ExecM.BoundsOutputIds.bind (outputIds_getState c) nextId_getState (fun st => ?_)
  split
  · exact outputIds_throw _ _
  · refine ExecM.BoundsOutputIds.bind (outputIds_get c) nextId_get (fun before => ?_)
    split
    · exact outputIds_throw _ _
    · exact outputIds_pure _ _

theorem outputIds_checkStorageStake (c : ReceiptCtx) (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).BoundsOutputIds c := by
  unfold checkStorageStake
  refine ExecM.BoundsOutputIds.bind (outputIds_getState c) nextId_getState (fun st => ?_)
  split
  · dsimp only
    split
    · exact outputIds_throw _ _
    · exact outputIds_pure _ _
  · exact outputIds_pure _ _

theorem outputIds_runReceiptAction (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).BoundsOutputIds c := by
  unfold runReceiptAction
  refine ExecM.BoundsOutputIds.bind (outputIds_fee _ _ _) (nextId_fee _ _) (fun _ => ?_)
  refine ExecM.BoundsOutputIds.bind (outputIds_checkReceiptAction _ _ _) (nextId_checkReceiptAction _ _ _) (fun _ => ?_)
  intro before hcallbacks h
  exact applyAction_outputIds c isLast action before h hcallbacks

theorem outputIds_runReceiptActionAt (c : ReceiptCtx) (onlyAction isLast : Bool)
    (action : Action) (index : Nat) : (runReceiptActionAt c onlyAction isLast action index).BoundsOutputIds c := by
  cases action with
  | createAccount  => exact outputIds_runReceiptAction c onlyAction isLast (.createAccount)
  | deployContract code => exact outputIds_runReceiptAction c onlyAction isLast (.deployContract code)
  | transfer amount => exact outputIds_runReceiptAction c onlyAction isLast (.transfer amount)
  | stake amount pk => exact outputIds_runReceiptAction c onlyAction isLast (.stake amount pk)
  | addKey pk key => exact outputIds_runReceiptAction c onlyAction isLast (.addKey pk key)
  | deleteKey pk => exact outputIds_runReceiptAction c onlyAction isLast (.deleteKey pk)
  | useGlobalContract contract => exact outputIds_runReceiptAction c onlyAction isLast (.useGlobalContract contract)
  | deleteAccount beneficiary => exact outputIds_runReceiptAction c onlyAction isLast (.deleteAccount beneficiary)
  | functionCall method args gas deposit =>
    intro before hcallbacks h
    cases hs : actionRandomSeed c index with
    | error error =>
      simp only [runReceiptActionAt, hs]
      exact h
    | ok seed =>
      simp only [runReceiptActionAt, hs]
      exact outputIds_runReceiptAction { c with vmRandomSeed := some seed } onlyAction isLast
        (.functionCall method args gas deposit) before hcallbacks h

theorem outputIds_failureIndex (c : ReceiptCtx) (index : Option Nat) :
    (modify fun e => { e with failureIndex := index } : ExecM Unit).BoundsOutputIds c := by
  intro before _ h
  exact h

theorem outputIds_runReceiptActionList (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action)
    (index : Nat) : (runReceiptActionList c onlyAction actions index).BoundsOutputIds c := by
  induction actions generalizing index with
  | nil => exact outputIds_pure _ _
  | cons action rest ih =>
    refine ExecM.BoundsOutputIds.bind (outputIds_failureIndex c (some index)) (nextId_failureIndex _) (fun _ => ?_)
    exact ExecM.BoundsOutputIds.bind (outputIds_runReceiptActionAt c onlyAction rest.isEmpty action index)
      (nextId_runReceiptActionAt _ _ _ _ _) (fun _ => ih (index + 1))

theorem outputIds_receiptActionBody (c : ReceiptCtx) : (receiptActionBody c).BoundsOutputIds c := by
  unfold receiptActionBody
  refine ExecM.BoundsOutputIds.bind (outputIds_fee _ _ _) (nextId_fee _ _) (fun _ => ?_)
  refine ExecM.BoundsOutputIds.bind (outputIds_runReceiptActionList c _ _ _) (nextId_runReceiptActionList _ _ _ _) (fun _ => ?_)
  exact ExecM.BoundsOutputIds.bind (outputIds_failureIndex c none) (nextId_failureIndex _)
    (fun _ => outputIds_checkStorageStake _ _ _)

theorem runReceiptActions_outputIds (c : ReceiptCtx) (st : ChainState) (hcallbacks : c.CallbackIdsBelow st.nextId) :
    (runReceiptActions c st).1.OutputIdsBelowNext := by
  have hp := outputIds_receiptActionBody c { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } hcallbacks
    (by intro receipt hm; contradiction)
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId, storageAccounting := c.ap.storageAccounting } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he] using hp

end Near
