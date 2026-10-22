import Std

namespace SputnikDAO2

/-! The successful arithmetic branch of `WeightOrRatio::to_weight` in
`sputnikdao2/src/policy.rs`. Values are mathematical naturals here; the
correspondence to Rust u128 needs the bounds below. -/

def maxU32 : Nat := 2 ^ 32 - 1
def maxU64 : Nat := 2 ^ 64 - 1
def maxU128 : Nat := 2 ^ 128 - 1

inductive WeightOrRatio where
  | weight (amount : Nat)
  | ratio (numerator denominator : Nat)
  deriving Repr, DecidableEq

def validRatio (numerator denominator total : Nat) : Prop :=
  numerator ≤ maxU64 ∧ 0 < denominator ∧ denominator ≤ maxU64 ∧
  total ≤ maxU128 ∧ numerator * total < maxU128

def toWeight (choice : WeightOrRatio) (total : Nat) : Nat :=
  match choice with
  | .weight amount => min amount total
  | .ratio numerator denominator =>
      min (numerator * total / denominator + 1) total

def voteThreshold (quorum : Nat) (choice : WeightOrRatio) (total : Nat) : Nat :=
  max quorum (toWeight choice total)

inductive Decision where
  | inProgress | approved | rejected | removed
  deriving Repr, DecidableEq

-- Per-role branch of `Policy::proposal_status`, after the expiry and role-kind
-- checks. The source tests approval first, then rejection, then removal.
def decideRole (threshold approvals rejections removals : Nat) : Decision :=
  if approvals ≥ threshold then .approved
  else if rejections ≥ threshold then .rejected
  else if removals ≥ threshold then .removed
  else .inProgress

-- The caller supplies a vector of allowed role names. The source iterates that
-- vector and returns on the first decisive role.
def firstDecisive : List Decision → Decision
  | [] => .inProgress
  | .inProgress :: rest => firstDecisive rest
  | decision :: _ => decision

def expired (submission period now : Nat) : Bool :=
  submission + period < now

end SputnikDAO2
