import Model.TransferExecution

namespace SputnikDAO2

/-! `ProposalKind::FunctionCall` execution after an approved vote or
successful finalization. All actions are appended to one promise batch in
source order, including when the list is empty. The batch is followed by the
same generic proposal callback used for transfers. This is a receipt-plan
projection, not a proof of host execution or JSON/Borsh parsing. -/

structure FunctionCallAction where
  method : String
  args : List UInt8
  deposit : Nat
  gas : Nat
  deriving Repr, DecidableEq

structure FunctionCallExecutionPlan where
  receiver : String
  actions : List FunctionCallAction
  callback : TransferCallbackPlan
  immediateBondRefund : Bool
  deriving Repr, DecidableEq

def planFunctionCall (receiver : String) (actions : List FunctionCallAction)
    (current : String) (proposalId : Nat) : FunctionCallExecutionPlan :=
  ⟨receiver, actions,
    ⟨current, "on_proposal_callback", proposalId, 0, ftTransferGas⟩,
    false⟩

-- The callback implementation is shared by all promise-returning proposals
-- other than BountyDone. FunctionCall therefore has precisely this branch.
def finishFunctionCallCallback := finishTransferCallback

end SputnikDAO2
