import Spec.Invariants

/-!
# Availability

The contract never refuses what it promises: a holder can always unwrap, and
a depositor can always wrap.
-/

namespace WNear

/-- A registered account holding at least `amount` wNEAR that attaches exactly
1 yoctoNEAR succeeds in the unmetered `near_withdraw(amount)` model: its
balance and supply drop by `amount`, a transfer of `amount + 1` yoctoNEAR is
scheduled, and the return delegates to that payout receipt (local index 0).
This does not assert eventual delivery or successful payout. The bound
`amount + 1 < 2^128` excludes the one value whose refund would overflow. -/
@[blueprint "spec:withdraw-available"
  (statement := /-- If $s$ satisfies \cref{def:inv}, the predecessor is registered with balance at least $a$, exactly 1 yoctoNEAR is attached and $a + 1 < 2^{128}$, then \texttt{near\_withdraw}$(a)$ succeeds: the predecessor's balance and the supply drop by $a$, a single transfer of $a + 1$ yoctoNEAR is scheduled to the predecessor, the return selects that transfer (receipt index 0), and the log is \texttt{Withdraw a NEAR from P}. -/)]
def WithdrawAvailable : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (amount : Nat),
    Inv cfg s →
    env.predecessor ∈ s.registered → amount ≤ s.balance env.predecessor →
    env.attachedDeposit = 1 → amount + 1 < u128Bound →
    step cfg (some s) env (.nearWithdraw amount) =
      .ok { state := { s.setBalance env.predecessor (s.balance env.predecessor - amount) with
                       totalSupply := s.totalSupply - amount },
            promises := [.transfer env.predecessor (amount + 1)],
            ret := .promise 0,
            logs := [s!"Withdraw {amount} NEAR from {env.predecessor}"] }

/-- A positive deposit that fits the supply always succeeds in `near_deposit`
when the depositor is registered or the deposit covers the registration fee.
The depositor ends up registered, credited with the deposit minus the fee it
paid (if any), and no NEAR leaves the contract. -/
@[blueprint "spec:deposit-available"
  (statement := /-- If $s$ satisfies \cref{def:inv}, the attached deposit $d$ is positive, $\mathit{totalSupply} + d < 2^{128}$, and the predecessor is registered or $d \ge \mathrm{storageMin}$, then \texttt{near\_deposit} succeeds: the predecessor ends registered with balance increased by $d$ minus the fee it paid, and no promise is created. -/)]
def DepositAvailable : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env),
    Inv cfg s → 0 < env.attachedDeposit →
    s.totalSupply + env.attachedDeposit < u128Bound →
    (env.predecessor ∈ s.registered ∨ s.storageMin ≤ env.attachedDeposit) →
    ∃ o, step cfg (some s) env .nearDeposit = .ok o ∧
      env.predecessor ∈ o.state.registered ∧
      o.state.balance env.predecessor
        + (if env.predecessor ∈ s.registered then 0 else s.storageMin)
        = s.balance env.predecessor + env.attachedDeposit ∧
      o.promises = []

end WNear
