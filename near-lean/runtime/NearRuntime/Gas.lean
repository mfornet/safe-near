import NearRuntime.Fees

/-! Receipt gas purchase, burn and refund accounting from the pinned runtime's
`config.rs::tx_cost` and `lib.rs::refund_unspent_gas_and_deposits`.
The protocol feature and all numeric parameters come from generated data. -/

namespace Near.Gas

open Wasm.Near

structure Settlement where
  refund : Nat
  tokensBurnt : Nat
  rewardPrice : Nat
  creationCharge : Nat
  penalty : Nat
  deriving Repr, BEq, Inhabited

def refundPenalty (cfg : FeesConfig) (gross : Nat) : Nat :=
  let (num, den) := cfg.gasRefundPenalty
  min gross (max (gross * num / den) cfg.minGasRefundPenalty)

/-- The fee balance for a non-system action receipt. `used` includes gas
attached onward. On failure the caller passes burnt gas as used gas. -/
def settle (cfg : RuntimeConfig) (blockPrice purchase receiptGas burnt used : Nat)
    (createdAccount : Bool) : Settlement :=
  let burnPrice := if cfg.accountCostIncrease then min purchase blockPrice else blockPrice
  let gross := receiptGas - used
  let penaltyPrice := if cfg.accountCostIncrease then burnPrice else purchase
  let penalty := refundPenalty cfg.fees gross * penaltyPrice
  let surplus := (purchase - burnPrice) * burnt
  let deficit := (burnPrice - purchase) * burnt
  let creationCharge :=
    if createdAccount && cfg.accountCostIncrease then
      min surplus
        (cfg.accountCreationCharge - cfg.fees.actionFees.createAccount.execution * burnPrice)
    else 0
  let burnedRefund := if cfg.accountCostIncrease then surplus - creationCharge else 0
  { refund := gross * purchase - penalty + burnedRefund
    tokensBurnt :=
      burnt * burnPrice - deficit + penalty + creationCharge +
        (if cfg.accountCostIncrease then 0 else surplus)
    rewardPrice := if cfg.accountCostIncrease then burnPrice else purchase
    creationCharge
    penalty }

end Near.Gas
