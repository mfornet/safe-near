import Std

namespace SputnikDAO2

structure BondPolicyAmounts where
  proposalBond : Nat
  bountyBond : Nat
  deriving Repr, DecidableEq

structure BondTransfer where
  receiver : String
  amount : Nat
  deriving Repr, DecidableEq

structure BondReturn where
  lockedAfter : Nat
  detachedTransfers : List BondTransfer
  returnedTransfer : BondTransfer
  deriving Repr, DecidableEq

-- `internal_return_bonds` reads CURRENT policy amounts, not per-proposal
-- historical deposits. For BountyDone it detaches the bounty-bond transfer,
-- then returns a separate proposal-bond promise to its caller.
def returnProposalBonds (locked : Nat) (policy : BondPolicyAmounts)
    (proposer : String) (isBountyDone : Bool) : BondReturn :=
  if isBountyDone then
    ⟨(locked - policy.bountyBond) - policy.proposalBond,
      [⟨proposer, policy.bountyBond⟩],
      ⟨proposer, policy.proposalBond⟩⟩
  else
    ⟨locked - policy.proposalBond, [],
      ⟨proposer, policy.proposalBond⟩⟩

def totalScheduledRefund (result : BondReturn) : Nat :=
  (result.detachedTransfers.map BondTransfer.amount).sum +
    result.returnedTransfer.amount

end SputnikDAO2
