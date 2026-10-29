import Bridge.Methods.NearDepositModel
import Bridge.Functions.DepositBody

/-!
# The initialized deposit classifier agrees with the model

`model_eq_dcase` connects every branch of the binary's pure classifier to the
model, including the exact state and log on success. Word decoding and the
represented storage are handled separately at the method boundary.
-/

namespace WNear.Binary.NearDepositMethod

open WNear.Binary.DepositBody

/-- The account lookup exposed to the binary's pure classifier. -/
def modelReg (s : WNear.State) (a : WNear.AccountId) : Option Nat :=
  if a ∈ s.registered then some (s.balance a) else none

/-- The successful mint, after charging a new account its registration fee. -/
def mintedOutcome (s : WNear.State) (env : WNear.Env) : WNear.Outcome :=
  let reg := modelReg s env.predecessor
  let amount := amountOf env.attachedDeposit reg s.storageMin
  let base := if env.predecessor ∈ s.registered then s else s.register env.predecessor
  { state := { base.setBalance env.predecessor (reg.getD 0 + amount) with
        totalSupply := s.totalSupply + amount }
    logs := [s!"Deposit {amount} NEAR to {env.predecessor}"] }

/-- Each binary branch denotes the corresponding model result. -/
def caseResult (c : DCase) (s : WNear.State) (env : WNear.Env) : WNear.M WNear.Outcome :=
  match c with
  | .pos => .error .requiresPositiveDeposit
  | .small => .error .depositTooSmall
  | .bal => .error .balanceOverflow
  | .sup => .error .totalSupplyOverflow
  | .ok => .ok (mintedOutcome s env)

/-- All five outcomes of `dcase` agree with `nearDeposit`, in the same check order. -/
theorem model_eq_dcase (s : WNear.State) (env : WNear.Env) :
    WNear.nearDeposit s env = caseResult
      (dcase env.attachedDeposit (modelReg s env.predecessor) s.storageMin s.totalSupply) s env := by
  by_cases hr : env.predecessor ∈ s.registered
  · rw [nearDeposit_registered s env hr]
    by_cases hd : env.attachedDeposit = 0 <;>
      by_cases hb : 2 ^ 128 ≤ s.balance env.predecessor + env.attachedDeposit <;>
      by_cases ht : 2 ^ 128 ≤ s.totalSupply + env.attachedDeposit <;>
      simp only [dcase, modelReg, if_pos hr, amountOf, Option.getD_some,
        WNear.u128Bound, hd, hb, ht, Option.some_ne_none, false_and, ite_true, ite_false,
        caseResult, mintedOutcome]
  · by_cases hd : env.attachedDeposit = 0
    · rw [nearDeposit_zero s env hd]
      simp only [dcase, hd, Nat.reduceEqDiff, ite_true, caseResult]
    · have hp : 0 < env.attachedDeposit := Nat.pos_of_ne_zero hd
      by_cases hm : env.attachedDeposit < s.storageMin
      · rw [nearDeposit_too_small s env hr hp hm]
        simp only [dcase, modelReg, if_neg hr, if_neg hd, and_self, hm, ite_true, caseResult]
      · rw [nearDeposit_unregistered s env hr hp (Nat.le_of_not_lt hm)]
        by_cases hb : 2 ^ 128 ≤ env.attachedDeposit - s.storageMin <;>
          by_cases ht : 2 ^ 128 ≤ s.totalSupply + (env.attachedDeposit - s.storageMin) <;>
          simp only [dcase, modelReg, if_neg hr, if_neg hd, hm, and_false, ite_false,
            amountOf, Option.getD_none, Nat.zero_add, WNear.u128Bound, hb, ht,
            ite_true, caseResult, mintedOutcome]

end WNear.Binary.NearDepositMethod
