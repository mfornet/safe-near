import Model.Upgrade
import Model.ProposalBonds

namespace SputnikDAO2

/-! The two approved upgrade proposal kinds in
`internal_execute_proposal`. Both helpers schedule an independent call and
return `Value(())`; the enclosing helper then returns the current proposal
bond immediately. These plans describe scheduled receipts, not their success.
JSON encoding of the factory arguments and AccountId parsing are inputs. -/

structure UpgradeProposalCall where
  receiver : String
  method : String
  args : CodeBytes
  attachedDeposit : Nat
  staticGas : Nat
  gasWeight : Nat
  deriving Repr, DecidableEq

structure UpgradeProposalPlan where
  independentCall : UpgradeProposalCall
  immediateBondReturn : BondReturn
  callbackScheduled : Bool
  deriving Repr, DecidableEq

-- `UpgradeSelf` routes to the current account's immediate parent, ignoring
-- the stored FACTORY override. `factoryArgs` is the SDK JSON encoding of
-- `{account_id: current, code_hash: hash}`, supplied by refinement.
def executeUpgradeSelf (current : String) (_storedFactory : FactoryInfo)
    (factoryArgs : CodeBytes) (locked : Nat) (policy : BondPolicyAmounts)
    (proposer : String) : Option UpgradeProposalPlan := do
  let parent ← factoryParentSuffix current
  some {
    independentCall := ⟨parent, "update", factoryArgs, 0, 0, 1⟩
    immediateBondReturn := returnProposalBonds locked policy proposer false
    callbackScheduled := false }

-- `UpgradeRemote` reads code from a raw hash key before creating its call.
-- A missing raw key aborts; an owner-index record alone is insufficient.
def executeUpgradeRemote (receiver method : String)
    (rawBlob : Option CodeBytes) (locked : Nat)
    (policy : BondPolicyAmounts) (proposer : String) :
    Option UpgradeProposalPlan := do
  let code ← rawBlob
  some {
    independentCall := ⟨receiver, method, code, 0, 0, 0⟩
    immediateBondReturn := returnProposalBonds locked policy proposer false
    callbackScheduled := false }

end SputnikDAO2
