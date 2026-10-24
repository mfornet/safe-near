import NearRuntime.RoutingInvariants
import NearRuntime.NewActionFunding

namespace Near
open Wasm.Near

theorem ChainState.account?_removeAccount_ne (st : ChainState) (receiver id : AccountId)
    (hne : receiver ≠ id) : (st.removeAccount receiver).account? id = st.account? id :=
  Assoc.lookup_erase_ne st.accounts receiver id hne

/-- A successful VM commit changes only its own account record. Promise effects
are emitted as receipts; they do not directly mutate other receiver accounts. -/
theorem commitFunctionCall_account_ne (exec : Exec) (c : ReceiptCtx) (account : Account)
    (outcome : Wasm.Near.VMOutcome) (isLast : Bool) (effects : FunctionCallEffects)
    (heffects : functionCallEffects c account outcome isLast exec.state = .ok effects) (id : AccountId) (hne : c.receipt.receiverId ≠ id) :
    (exec.commitFunctionCall outcome effects).state.account? id = exec.state.account? id := by
  have hf := congrArg (fun state : ChainState => state.account? id) (commitFunctionCall_frame exec c account outcome isLast effects heffects)
  change (exec.commitFunctionCall outcome effects).state.account? id =
    (exec.state.setAccount c.receipt.receiverId _).account? id at hf
  rw [ChainState.account?_setAccount_ne _ _ _ _ hne] at hf
  exact hf

theorem transferCreditState_account_ne (c : ReceiptCtx) (st : ChainState) (account : Account)
    (amount : Nat) (id : AccountId) (hne : c.receipt.receiverId ≠ id) :
    (transferCreditState c st account amount).account? id = st.account? id := by
  unfold transferCreditState
  dsimp only
  split
  · rw [refundAllowance_account]
    exact ChainState.account?_setAccount_ne _ _ _ _ hne
  · exact ChainState.account?_setAccount_ne _ _ _ _ hne

theorem addKeyMetadataState_account_ne (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey)
    (key : AccessKey) (x : AccountId) (hne : c.receipt.receiverId ≠ x) :
    (addKeyMetadataState c st account pk key).account? x = st.account? x := by
  unfold addKeyMetadataState
  split
  · change Assoc.lookup _ x = _
    rw [(ChainState.foldl_setGasKeyNonce_frame _ _ _ _ _).1]
    exact ChainState.account?_setAccount_ne _ _ _ _ hne
  · exact ChainState.account?_setAccount_ne _ _ _ _ hne

theorem deleteKeyMetadataState_account_ne (c : ReceiptCtx) (st : ChainState) (account : Account) (pk : PublicKey)
    (key : AccessKey) (x : AccountId) (hne : c.receipt.receiverId ≠ x) :
    (deleteKeyMetadataState c st account pk key).account? x = st.account? x := by
  unfold deleteKeyMetadataState
  split <;> exact ChainState.account?_setAccount_ne _ _ _ _ hne

theorem deleteAccountFundedResult_account_ne (c : ReceiptCtx) (before : Exec) (account : Account)
    (beneficiary : AccountId) (x : AccountId) (hne : c.receipt.receiverId ≠ x) :
    (deleteAccountFundedResult c before account beneficiary).state.account? x = before.state.account? x := by
  unfold deleteAccountFundedResult
  dsimp only
  split <;> exact ChainState.account?_removeAccount_ne _ _ _ hne

/-- Exact local account isolation on all raw action outcomes, including errors
with tentative changes. This does not claim isolation from emitted future receipts. -/
theorem applyAction_account_ne (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (id : AccountId) (hne : c.receipt.receiverId ≠ id) :
    ((applyAction c isLast action).run.run before).2.state.account? id = before.state.account? id := by
  cases action with
  | createAccount =>
    rw [applyCreateAccount_run]
    repeat' (first | rfl | exact ChainState.account?_setAccount_ne _ _ _ _ hne | split)
  | deployContract code =>
    rw [applyDeployContract_run]
    repeat' (first | rfl | exact ChainState.account?_setAccount_ne _ _ _ _ hne | split)
  | functionCall method args gas deposit =>
    change ((applyFunctionCall c method args gas deposit isLast).run.run before).2.state.account? id = _
    rw [applyFunctionCall_run]
    repeat' (first | rfl | exact commitFunctionCall_account_ne _ _ _ _ _ _ (by assumption) _ hne | split | (dsimp only; split))
  | transfer amount =>
    rw [applyTransfer_run]
    repeat' (first | rfl | exact transferCreditState_account_ne _ _ _ _ _ hne |
      exact ChainState.account?_setAccount_ne _ _ _ _ hne | split)
  | stake amount pk =>
    cases ha : before.state.account? c.receipt.receiverId <;>
      simp [-StateT.run_bind, applyAction, getAccount, getState, ha]
    repeat' (first | rfl | split)
  | addKey pk key =>
    rw [applyAddKey_run]
    repeat' (first | rfl | exact addKeyMetadataState_account_ne _ _ _ _ _ _ hne | split)
  | deleteKey pk =>
    rw [applyDeleteKey_run]
    repeat' (first | rfl | exact deleteKeyMetadataState_account_ne _ _ _ _ _ _ hne | split)
  | useGlobalContract contract =>
    rw [applyUseGlobalContract_run]
    repeat' (first | rfl | exact ChainState.account?_setAccount_ne _ _ _ _ hne | split)
  | deployGlobalContract code mode =>
    rw [applyDeployGlobalContract_run]
    repeat' (first | rfl | exact deployGlobalResult_account_ne _ _ _ _ _ hne | split)
  | transferToGasKey pk deposit =>
    rw [applyTransferToGasKey_run]
    repeat' (first | rfl | exact gasKeyDeposit_account (by assumption) _ | split)
  | withdrawFromGasKey pk amount =>
    rw [applyWithdrawFromGasKey_run]
    repeat' (first | rfl | exact (gasKeyWithdrawal_account (by assumption)).2 _ hne | split)
  | deleteAccount beneficiary =>
    rw [applyDeleteAccount_run]
    repeat' (first | rfl | exact deleteAccountFundedResult_account_ne _ _ _ _ _ hne | split)
  | delegate sender receiver inner nonce nonceIndex maxBlockHeight pk signature v2 =>
    change ((applyDelegateAction c _).run.run before).2.state.account? id = _
    rw [applyDelegateAction_run]
    repeat' (first | rfl | (have h := delegateState_account (by assumption) id; exact h) | split)

end Near
