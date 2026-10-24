import NearRuntime.RoutingInvariants

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

/-- Exact local account isolation on all raw action outcomes, including errors
with tentative changes. This does not claim isolation from emitted future receipts. -/
-- TODO(proof): adapt the cloned proof
theorem applyAction_account_ne (c : ReceiptCtx) (isLast : Bool) (action : Action) (before : Exec)
    (id : AccountId) (hne : c.receipt.receiverId ≠ id) :
    ((applyAction c isLast action).run.run before).2.state.account? id = before.state.account? id := by
  sorry

end Near
