import Model.Policy

namespace SputnikDAO2

-- One bounty id's claims. `paidBond` is ghost history: the on-chain claim
-- record does not store the bond paid when it was created.
structure BondClaim where
  account : String
  start : Nat
  deadline : Nat
  completed : Bool
  paidBond : Nat
  deriving Repr, DecidableEq

structure BountyBondState where
  claims : List BondClaim
  claimCount : Nat
  locked : Nat
  deriving Repr, DecidableEq

def removeFirstClaim : List BondClaim → String → Option (BondClaim × List BondClaim)
  | [], _ => none
  | claim :: rest, account =>
      if claim.account == account then some (claim, rest)
      else match removeFirstClaim rest account with
        | none => none
        | some (found, remaining) => some (found, claim :: remaining)

def bountyClaim (state : BountyBondState) (account : String)
    (now duration maxDeadline times policyBond attached : Nat) :
    Option BountyBondState :=
  if attached != policyBond || state.claimCount ≥ times ||
      duration > maxDeadline then none
  else some {
    claims := state.claims ++ [⟨account, now, duration, false, attached⟩]
    claimCount := state.claimCount + 1
    locked := min (state.locked + attached) maxU128 }

-- Refund is `some amount` only within the forgiveness period. The source
-- subtracts the CURRENT policy bond, not the historical attached bond, and
-- leaves locked unchanged after the forgiveness period. `none` for the whole
-- result represents a missing claim, checked time underflow, or count underflow.
def bountyGiveup (state : BountyBondState) (account : String)
    (now forgiveness currentBond : Nat) :
    Option (BountyBondState × Option Nat) := Id.run do
  let some (claim, remaining) := removeFirstClaim state.claims account |
    return none
  if now < claim.start || state.claimCount == 0 then return none
  let count := state.claimCount - 1
  if now - claim.start > forgiveness then
    return some (⟨remaining, count, state.locked⟩, none)
  else
    return some (⟨remaining, count, state.locked - currentBond⟩,
      some currentBond)

end SputnikDAO2
