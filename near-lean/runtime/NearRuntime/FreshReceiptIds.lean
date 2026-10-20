import NearRuntime.BlockIdentifierBounds

namespace Near
open Wasm.Near

/-- Envelope identities are distinct and lie in a half-open allocation interval.
Dependency ids may be shared and are deliberately not required to be unique. -/
structure ReceiptList.FreshIds (lower upper : Nat) (receipts : List Receipt) : Prop where
  unique : (receipts.map (·.receiptId)).Nodup
  bounds : ∀ receipt ∈ receipts, lower ≤ receipt.receiptId ∧ receipt.receiptId < upper

theorem ReceiptList.FreshIds.empty (lower upper : Nat) : ReceiptList.FreshIds lower upper [] := by
  constructor <;> simp

theorem ReceiptList.FreshIds.mono_upper {lower before after : Nat} {receipts : List Receipt}
    (h : ReceiptList.FreshIds lower before receipts) (hle : before ≤ after) :
    ReceiptList.FreshIds lower after receipts := by
  refine ⟨h.unique, ?_⟩
  intro receipt hm
  exact ⟨(h.bounds receipt hm).1, (h.bounds receipt hm).2.trans_le hle⟩

/-- Consecutive allocation intervals make append collision-free. -/
theorem ReceiptList.FreshIds.append {lower middle upper : Nat} {before after : List Receipt}
    (hbefore : ReceiptList.FreshIds lower middle before) (hafter : ReceiptList.FreshIds middle upper after)
    (hlower : lower ≤ middle) (hupper : middle ≤ upper) :
    ReceiptList.FreshIds lower upper (before ++ after) := by
  constructor
  · rw [List.map_append, List.nodup_append]
    refine ⟨hbefore.unique, hafter.unique, ?_⟩
    intro first hfirst last hlast he
    obtain ⟨r, hr, hri⟩ := List.mem_map.mp hfirst
    obtain ⟨s, hs, hsi⟩ := List.mem_map.mp hlast
    have hb := (hbefore.bounds r hr).2
    have ha := (hafter.bounds s hs).1
    rw [hri] at hb
    rw [hsi, ← he] at ha
    exact Nat.not_le_of_lt hb ha
  · intro receipt hm
    rcases List.mem_append.mp hm with hold | hnew
    · exact ⟨(hbefore.bounds receipt hold).1, (hbefore.bounds receipt hold).2.trans_le hupper⟩
    · exact ⟨hlower.trans (hafter.bounds receipt hnew).1, (hafter.bounds receipt hnew).2⟩

def Exec.FreshReceiptIds (lower : Nat) (exec : Exec) : Prop :=
  ReceiptList.FreshIds lower exec.state.nextId exec.newReceipts

theorem Exec.FreshReceiptIds.of_frame {lower : Nat} {before after : Exec} (h : before.FreshReceiptIds lower)
    (hreceipts : after.newReceipts = before.newReceipts) (hnext : before.state.nextId ≤ after.state.nextId) :
    after.FreshReceiptIds lower := by
  change ReceiptList.FreshIds lower after.state.nextId after.newReceipts
  rw [hreceipts]
  exact h.mono_upper hnext

theorem Exec.addBalanceRefund_freshIds (exec : Exec) (receiver : AccountId) (amount lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.addBalanceRefund receiver amount).FreshReceiptIds lower := by
  apply ReceiptList.FreshIds.append h _ hfloor (Nat.le_succ _)
  constructor
  · simp
  · intro receipt hm
    have he := List.mem_singleton.mp hm
    subst receipt
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩

theorem Exec.addGasRefund_freshIds (exec : Exec) (receiver : AccountId) (pk : PublicKey) (amount lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.addGasRefund receiver pk amount).FreshReceiptIds lower := by
  apply ReceiptList.FreshIds.append h _ hfloor (Nat.le_succ _)
  constructor
  · simp
  · intro receipt hm
    have he := List.mem_singleton.mp hm
    subst receipt
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩

theorem commitFunctionCall_freshIds (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : VMOutcome) (isLast : Bool) (lower : Nat)
    (h : exec.FreshReceiptIds lower) (hfloor : lower ≤ exec.state.nextId) :
    (exec.commitFunctionCall c account outcome isLast).FreshReceiptIds lower := by
  let initial := (exec.state.setAccount c.receipt.receiverId
    { account with amount := outcome.balance, storageUsage := outcome.storageUsage }).setContractStorage
      c.receipt.receiverId outcome.storage
  apply ReceiptList.FreshIds.append h _ hfloor (commitFunctionCall_nextId_mono exec c account outcome isLast)
  exact ⟨materializeFunctionCall_receiptIds_nodup c isLast outcome initial,
    materializeFunctionCall_receiptId_bounds c isLast outcome initial⟩

/-- Raw actions retain unique emitted identities and allocate subsequent ones
outside the entire prior output interval, even on failed attempts. -/
theorem applyAction_freshIds (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec) (lower : Nat)
    (h : before.FreshReceiptIds lower) (hfloor : lower ≤ before.state.nextId) :
    ((applyAction c isLast action).run.run before).2.FreshReceiptIds lower := by
  cases action with
  | createAccount => rw [applyCreateAccount_run]; repeat' (first | exact h | split)
  | deployContract code => rw [applyDeployContract_run]; repeat' (first | exact h | split)
  | functionCall method args gas deposit =>
    rw [show applyAction c isLast (.functionCall method args gas deposit) =
      applyFunctionCall c method args gas deposit isLast from rfl, applyFunctionCall_run]
    split
    · exact h
    · split
      · exact h
      · dsimp only
        split
        · exact h
        · exact commitFunctionCall_freshIds _ _ _ _ _ _ h hfloor
  | transfer amount =>
    rw [applyTransfer_run]
    split
    · rename_i account haccount
      apply Exec.FreshReceiptIds.of_frame (after := { before with state := transferCreditState c before.state account amount }) h rfl
      exact Nat.le_of_eq (transferCreditState_nextId _ _ _ _).symm
    · split
      · exact h
      · split <;> exact h
  | stake amount pk =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-ExceptT.run_bind, -StateT.run_bind, applyAction, getAccount, getState, ha]
    repeat' (first | exact h | split)
  | addKey pk key => rw [applyAddKey_run]; repeat' (first | exact h | split)
  | deleteKey pk => rw [applyDeleteKey_run]; repeat' (first | exact h | split)
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · exact Exec.addBalanceRefund_freshIds before beneficiary _ lower h hfloor

/-- A fixed allocation floor is retained while each operation reserves new ids. -/
def ExecM.PreservesFreshIds (lower : Nat) (operation : ExecM α) : Prop :=
  ∀ before, lower ≤ before.state.nextId → before.FreshReceiptIds lower →
    (operation.run.run before).2.FreshReceiptIds lower

theorem ExecM.PreservesFreshIds.bind {lower : Nat} {operation : ExecM α} {next : α → ExecM β}
    (hfirst : operation.PreservesFreshIds lower) (hmono : operation.NextIdMonotone)
    (hnext : ∀ value, (next value).PreservesFreshIds lower) : (operation >>= next).PreservesFreshIds lower := by
  intro before hfloor hbefore
  rw [execM_run_bind]
  have hp := hfirst before hfloor hbefore
  have hn := hmono before
  cases he : operation.run.run before with
  | mk result middle =>
    rw [he] at hp hn
    cases result with
    | error error => exact hp
    | ok value => exact hnext value middle (hfloor.trans hn) hp

theorem freshIds_pure (lower : Nat) (value : α) : (pure value : ExecM α).PreservesFreshIds lower := by
  intro before _ h; exact h

theorem freshIds_throw (lower : Nat) (error : RuntimeError) : (throw error : ExecM α).PreservesFreshIds lower := by
  intro before _ h; exact h

theorem freshIds_get (lower : Nat) : (get : ExecM Exec).PreservesFreshIds lower := by intro before _ h; exact h

theorem freshIds_getState (lower : Nat) : getState.PreservesFreshIds lower := by intro before _ h; exact h

theorem freshIds_fee (lower : Nat) (isRefund : Bool) (fee : Nat) : (chargeReceiptFee isRefund fee).PreservesFreshIds lower := by
  intro before _ h
  unfold chargeReceiptFee
  split <;> exact h

theorem freshIds_checkReceiptAction (lower : Nat) (c : ReceiptCtx) (onlyAction : Bool) (action : Action) :
    (checkReceiptAction c onlyAction action).PreservesFreshIds lower := by
  unfold checkReceiptAction
  refine ExecM.PreservesFreshIds.bind (freshIds_getState lower) nextId_getState (fun st => ?_)
  split
  · exact freshIds_throw _ _
  · refine ExecM.PreservesFreshIds.bind (freshIds_get lower) nextId_get (fun before => ?_)
    split
    · exact freshIds_throw _ _
    · exact freshIds_pure _ _

theorem freshIds_checkStorageStake (lower : Nat) (cfg : RuntimeConfig) (id : AccountId) :
    (checkStorageStake cfg id).PreservesFreshIds lower := by
  unfold checkStorageStake
  refine ExecM.PreservesFreshIds.bind (freshIds_getState lower) nextId_getState (fun st => ?_)
  split
  · dsimp only
    split
    · exact freshIds_throw _ _
    · exact freshIds_pure _ _
  · exact freshIds_pure _ _

theorem freshIds_runReceiptAction (lower : Nat) (c : ReceiptCtx) (onlyAction isLast : Bool) (action : Action) :
    (runReceiptAction c onlyAction isLast action).PreservesFreshIds lower := by
  unfold runReceiptAction
  refine ExecM.PreservesFreshIds.bind (freshIds_fee _ _ _) (nextId_fee _ _) (fun _ => ?_)
  refine ExecM.PreservesFreshIds.bind (freshIds_checkReceiptAction _ _ _ _) (nextId_checkReceiptAction _ _ _) (fun _ => ?_)
  intro before hfloor h
  exact applyAction_freshIds c isLast action before lower h hfloor

theorem freshIds_runReceiptActionList (lower : Nat) (c : ReceiptCtx) (onlyAction : Bool) (actions : List Action) :
    (runReceiptActionList c onlyAction actions).PreservesFreshIds lower := by
  induction actions with
  | nil => exact freshIds_pure _ _
  | cons action rest ih =>
    exact ExecM.PreservesFreshIds.bind (freshIds_runReceiptAction _ _ _ _ _)
      (nextId_runReceiptAction _ _ _ _) (fun _ => ih)

theorem freshIds_receiptActionBody (lower : Nat) (c : ReceiptCtx) : (receiptActionBody c).PreservesFreshIds lower := by
  unfold receiptActionBody
  refine ExecM.PreservesFreshIds.bind (freshIds_fee _ _ _) (nextId_fee _ _) (fun _ => ?_)
  exact ExecM.PreservesFreshIds.bind (freshIds_runReceiptActionList _ _ _ _) (nextId_runReceiptActionList _ _ _)
    (fun _ => freshIds_checkStorageStake _ _ _)

theorem runReceiptActions_freshIds (c : ReceiptCtx) (st : ChainState) :
    (runReceiptActions c st).1.FreshReceiptIds st.nextId := by
  have hp := freshIds_receiptActionBody st.nextId c { state := st, actorId := c.receipt.predecessorId }
    (Nat.le_refl _) (ReceiptList.FreshIds.empty _ _)
  cases he : (receiptActionBody c).run.run { state := st, actorId := c.receipt.predecessorId } with
  | mk result raw => cases result <;> simpa only [runReceiptActions, he] using hp

end Near
