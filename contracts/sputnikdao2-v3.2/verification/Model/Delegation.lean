import Model.Policy

namespace SputnikDAO2

def balanceOf : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (user, balance) :: rest, account =>
      if user == account then some balance else balanceOf rest account

def setBalance : List (String × Nat) → String → Nat → List (String × Nat)
  | [], account, amount => [(account, amount)]
  | (user, balance) :: rest, account, amount =>
      if user == account then (user, amount) :: rest
      else (user, balance) :: setBalance rest account amount

def balanceSum : List (String × Nat) → Nat
  | [] => 0
  | (_, balance) :: rest => balance + balanceSum rest

structure DelegationState where
  stakingId : Option String
  balances : List (String × Nat)
  total : Nat
  deriving Repr, DecidableEq

def coherentDelegation (state : DelegationState) : Prop :=
  state.total = balanceSum state.balances

-- Source uses NearToken::saturating_mul(16) for the exact registration deposit.
def registrationDeposit (byteCost : Nat) : Nat :=
  min (byteCost * 16) maxU128

-- These are successful, atomic source branches. `none` means a guard or
-- checked arithmetic failed; the exact Rust error type is left for a full
-- exported-method model. List storage is a logical projection of LookupMap.
def registerDelegation (state : DelegationState) (caller account : String)
    (deposit byteCost : Nat) : Option DelegationState :=
  if state.stakingId != some caller || deposit != registrationDeposit byteCost then none
  else some { state with balances := setBalance state.balances account 0 }

def delegate (state : DelegationState) (caller account : String)
    (amount : Nat) : Option DelegationState := Id.run do
  if state.stakingId != some caller then return none
  let some previous := balanceOf state.balances account | return none
  if previous + amount > maxU128 || state.total + amount > maxU128 then return none
  return some { state with
    balances := setBalance state.balances account (previous + amount)
    total := state.total + amount }

def undelegate (state : DelegationState) (caller account : String)
    (amount : Nat) : Option DelegationState := Id.run do
  if state.stakingId != some caller then return none
  let previous := (balanceOf state.balances account).getD 0
  if previous < amount || state.total < amount then return none
  return some { state with
    balances := setBalance state.balances account (previous - amount)
    total := state.total - amount }

end SputnikDAO2
