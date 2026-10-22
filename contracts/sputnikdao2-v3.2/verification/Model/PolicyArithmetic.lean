import Model.Policy
import Model.SyncGovernance
import Model.Status

namespace SputnikDAO2

/-! Exact checked-u128 arithmetic for the source's ratio branch. The
intermediate multiplication and the subsequent `+ 1` both occur before
`min`, so a capped final threshold alone does not make evaluation safe. -/

def checkedRatioWeight (numerator denominator total : Nat) : Option Nat := do
  if numerator > maxU64 || denominator == 0 || denominator > maxU64 ||
      total > maxU128 then none
  else
    let product := numerator * total
    if product > maxU128 then none
    else
      let quotient := product / denominator
      if quotient == maxU128 then none
      else some (min (quotient + 1) total)

def ratioArithmeticSafe (numerator denominator total : Nat) : Prop :=
  numerator ≤ maxU64 ∧ 0 < denominator ∧ denominator ≤ maxU64 ∧
    total ≤ maxU128 ∧ numerator * total ≤ maxU128 ∧
    numerator * total / denominator < maxU128

-- The source skips Everyone and stops at the first decisive role. A later
-- unsafe threshold is therefore evaluated only when prior roles continue.
def checkedRoleDecision (role : StatusRole) (totalSupply : Nat) :
    Option Decision :=
  match role.kind with
  | .everyone => some .inProgress
  | _ =>
      match role.threshold with
      | .weight _ => some (roleDecision role totalSupply)
      | .ratio numerator denominator => do
          let _ ← checkedRatioWeight numerator denominator
            (roleTotal role totalSupply)
          some (roleDecision role totalSupply)

def firstCheckedDecision (totalSupply : Nat) :
    List StatusRole → Option Decision
  | [] => some .inProgress
  | role :: rest => do
      let decision ← checkedRoleDecision role totalSupply
      if decision == .inProgress then firstCheckedDecision totalSupply rest
      else some decision

-- Complete source order around ratio arithmetic: status guard, checked u64
-- expiry sum, expiry return, then short-circuiting role evaluation. Account
-- lookup and policy-map resolution remain inputs through `StatusRole`.
def proposalStatusChecked (original : ProposalStatus)
    (submission period now totalSupply : Nat) (roles : List StatusRole) :
    Option ProposalStatus := do
  if original != .inProgress && original != .failed then none
  else if submission > maxU64 || period > maxU64 || now > maxU64 ||
      submission + period > maxU64 then none
  else if expired submission period now then some .expired
  else
    let decision ← firstCheckedDecision totalSupply roles
    some (if decision == .inProgress then original else decisionStatus decision)

end SputnikDAO2
