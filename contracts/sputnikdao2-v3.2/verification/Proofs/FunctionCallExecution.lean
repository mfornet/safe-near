import Model.FunctionCallExecution
import Proofs.TransferExecution

namespace SputnikDAO2

theorem function_call_preserves_action_order (receiver : String)
    (actions : List FunctionCallAction) (current : String) (id : Nat) :
    (planFunctionCall receiver actions current id).actions = actions := by rfl

theorem function_call_preserves_action_count (receiver : String)
    (actions : List FunctionCallAction) (current : String) (id : Nat) :
    (planFunctionCall receiver actions current id).actions.length =
      actions.length := by rfl

theorem empty_function_call_still_schedules_callback
    (receiver current : String) (id : Nat) :
    planFunctionCall receiver [] current id =
      ⟨receiver, [], ⟨current, "on_proposal_callback", id, 0, ftTransferGas⟩,
        false⟩ := by rfl

theorem function_call_callback_and_bond_timing (receiver : String)
    (actions : List FunctionCallAction) (current : String) (id : Nat) :
    (planFunctionCall receiver actions current id).callback =
      ⟨current, "on_proposal_callback", id, 0, ftTransferGas⟩ ∧
    (planFunctionCall receiver actions current id).immediateBondRefund = false := by
  exact ⟨rfl, rfl⟩

theorem function_call_success_refunds_current_bond
    (state : TransferCallbackState) (policy : BondPolicyAmounts)
    (h : state.proposalPresent = true) :
    finishFunctionCallCallback state true 1 .success policy =
      some ⟨.approved, state.locked - policy.proposalBond,
        some ⟨state.proposer, policy.proposalBond⟩⟩ := by
  exact transfer_callback_success_refunds_current_bond state policy h

theorem function_call_failure_keeps_lock
    (state : TransferCallbackState) (policy : BondPolicyAmounts)
    (h : state.proposalPresent = true) :
    finishFunctionCallCallback state true 1 .failure policy =
      some ⟨.failed, state.locked, none⟩ := by
  exact transfer_callback_failure_keeps_lock state policy h

end SputnikDAO2
