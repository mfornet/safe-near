import Model.TransferExecution

namespace SputnikDAO2

theorem native_transfer_ignores_message (receiver : String) (amount : Nat)
    (memo current : String) (first second : Option String) (id : Nat) :
    (planTransfer .near receiver amount memo first current id).primary =
      (planTransfer .near receiver amount memo second current id).primary := by
  rfl

theorem native_transfer_schedules_callback (receiver : String) (amount : Nat)
    (memo current : String) (message : Option String) (id : Nat) :
    planTransfer .near receiver amount memo message current id =
      ⟨.nearTransfer receiver amount,
        ⟨current, "on_proposal_callback", id, 0, ftTransferGas⟩,
        false⟩ := by rfl

theorem ft_transfer_without_message (token receiver : String) (amount : Nat)
    (memo current : String) (id : Nat) :
    (planTransfer (.fungible token) receiver amount memo none current id).primary =
      .ftCall token "ft_transfer" receiver amount memo none 1 ftTransferGas := by rfl

theorem ft_transfer_call_with_message (token receiver : String) (amount : Nat)
    (memo message current : String) (id : Nat) :
    (planTransfer (.fungible token) receiver amount memo (some message) current id).primary =
      .ftCall token "ft_transfer_call" receiver amount memo (some message)
        1 ftTransferGas := by rfl

theorem transfer_never_immediately_refunds (asset : TransferAsset)
    (receiver : String) (amount : Nat) (memo : String)
    (message : Option String) (current : String) (id : Nat) :
    (planTransfer asset receiver amount memo message current id).immediateBondRefund =
      false := by cases asset <;> rfl

theorem every_transfer_schedules_same_callback (asset : TransferAsset)
    (receiver : String) (amount : Nat) (memo : String)
    (message : Option String) (current : String) (id : Nat) :
    (planTransfer asset receiver amount memo message current id).callback =
      ⟨current, "on_proposal_callback", id, 0, ftTransferGas⟩ := by
  cases asset <;> rfl

theorem transfer_callback_missing_proposal (state : TransferCallbackState)
    (count : Nat) (result : CallbackResult) (policy : BondPolicyAmounts)
    (h : state.proposalPresent = false) :
    finishTransferCallback state true count result policy = none := by
  simp [finishTransferCallback, h]

theorem transfer_callback_requires_self (state : TransferCallbackState)
    (count : Nat) (result : CallbackResult) (policy : BondPolicyAmounts) :
    finishTransferCallback state false count result policy = none := by
  simp [finishTransferCallback]

theorem transfer_callback_requires_one_result (state : TransferCallbackState)
    (self : Bool) (count : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts) (h : count ≠ 1) :
    finishTransferCallback state self count result policy = none := by
  simp [finishTransferCallback, h]

theorem transfer_callback_success_refunds_current_bond
    (state : TransferCallbackState) (policy : BondPolicyAmounts)
    (h : state.proposalPresent = true) :
    finishTransferCallback state true 1 .success policy =
      some ⟨.approved, state.locked - policy.proposalBond,
        some ⟨state.proposer, policy.proposalBond⟩⟩ := by
  simp [finishTransferCallback, h, returnProposalBonds]

theorem transfer_callback_failure_keeps_lock
    (state : TransferCallbackState) (policy : BondPolicyAmounts)
    (h : state.proposalPresent = true) :
    finishTransferCallback state true 1 .failure policy =
      some ⟨.failed, state.locked, none⟩ := by
  simp [finishTransferCallback, h]

theorem successful_callback_has_no_status_guard
    (original : ProposalStatus) (locked : Nat) (proposer : String)
    (policy : BondPolicyAmounts) :
    finishTransferCallback ⟨true, original, proposer, locked⟩
      true 1 .success policy =
      some ⟨.approved, locked - policy.proposalBond,
        some ⟨proposer, policy.proposalBond⟩⟩ := by
  simp [finishTransferCallback, returnProposalBonds]

end SputnikDAO2
