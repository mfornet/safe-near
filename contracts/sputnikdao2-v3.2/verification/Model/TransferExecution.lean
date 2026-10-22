import Model.Proposal
import Model.ProposalBonds

namespace SputnikDAO2

/-! `ProposalKind::Transfer` execution and its non-BountyDone callback.
`convert_old_to_new_token` maps the empty string to NEAR and parses other
strings as AccountId; this model starts after successful token parsing.
FT JSON serialization, receipt execution and account solvency are external. -/

inductive TransferAsset where
  | near
  | fungible (token : String)
  deriving Repr, DecidableEq

inductive TransferPrimary where
  | nearTransfer (receiver : String) (amount : Nat)
  | ftCall (token method receiver : String) (amount : Nat)
      (memo : String) (message : Option String)
      (attachedDeposit prepaidGas : Nat)
  deriving Repr, DecidableEq

structure TransferCallbackPlan where
  receiver : String
  method : String
  proposalId : Nat
  attachedDeposit : Nat
  staticGas : Nat
  deriving Repr, DecidableEq

structure TransferExecutionPlan where
  primary : TransferPrimary
  callback : TransferCallbackPlan
  immediateBondRefund : Bool
  deriving Repr, DecidableEq

def ftTransferGas : Nat := 10 * 10 ^ 12

def planTransfer (asset : TransferAsset) (receiver : String)
    (amount : Nat) (memo : String) (message : Option String)
    (current : String) (proposalId : Nat) : TransferExecutionPlan :=
  let primary := match asset with
    | .near => TransferPrimary.nearTransfer receiver amount
    | .fungible token =>
        TransferPrimary.ftCall token
          (if message.isSome then "ft_transfer_call" else "ft_transfer")
          receiver amount memo message 1 ftTransferGas
  ⟨primary, ⟨current, "on_proposal_callback", proposalId, 0,
      ftTransferGas⟩, false⟩

structure TransferCallbackState where
  proposalPresent : Bool
  status : ProposalStatus
  proposer : String
  locked : Nat
  deriving Repr, DecidableEq

structure TransferCallbackResult where
  status : ProposalStatus
  locked : Nat
  returnedBondPromise : Option BondTransfer
  deriving Repr, DecidableEq

-- `on_proposal_callback` checks existence, the SDK private caller and exactly
-- one result, but does not check the stored proposal status. A successful
-- callback uses CURRENT policy bond values and returns a bond promise; a
-- failed callback stores Failed and retains the lock.
def finishTransferCallback (state : TransferCallbackState)
    (callerSelf : Bool) (resultCount : Nat) (result : CallbackResult)
    (policy : BondPolicyAmounts) : Option TransferCallbackResult := do
  if !state.proposalPresent || !callerSelf || resultCount != 1 then none else
  match result with
  | .success =>
      let refund := returnProposalBonds state.locked policy state.proposer false
      some ⟨.approved, refund.lockedAfter, some refund.returnedTransfer⟩
  | .failure => some ⟨.failed, state.locked, none⟩

end SputnikDAO2
