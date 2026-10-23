import Spec.Contract

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

/-! ## At the function-call boundary

The same guarantees for a real call: the context's predecessor, deposit and
callback results, followed by the runtime's checks. A withdrawal also needs
the account to pay the transfer and its storage stake afterwards; a deposit
creates no promise, so it fails only if the account cannot pay the stake of
its new storage. With `Refines`, these are statements about the binary. -/

open NearInterface in
/-- \cref{spec:withdraw-available} for a call: with the liquid balance covering
the transfer and the storage stake of the new state paid, `near_withdraw`
succeeds at the boundary with the same state, promise, return and log. -/
@[blueprint "spec:withdraw-available-boundary"
  (statement := /-- Under the hypotheses of \cref{spec:withdraw-available} for the context's predecessor and deposit, if the account's balance plus the deposit covers the transfer of $a + 1$ yoctoNEAR and the storage stake of the resulting state is paid, then the call \texttt{near\_withdraw}$(a)$ succeeds at the function-call boundary with the resulting state, the transfer, receipt index 0 as return, and the withdrawal log. -/)]
def WithdrawAvailableAtBoundary : Prop :=
  ∀ (cfg : Config) (s : State) (ctx : Context) (amount : Nat),
    let a := AccountId.ofNear ctx.predecessor
    let s' := { s.setBalance a (s.balance a - amount) with totalSupply := s.totalSupply - amount }
    Inv cfg s → a ∈ s.registered → amount ≤ s.balance a → ctx.attached = 1 →
    amount + 1 < u128Bound → amount ≤ ctx.balance →
    stakeDeficit ctx.protocol (usageAfter ctx (some s) s') (ctx.balance - amount) ctx.locked = 0 →
    contractStep ctx (some s) (.nearWithdraw amount) =
      .ok { state := s', promises := [.transfer a (amount + 1)], ret := .promise 0,
            logs := [s!"Withdraw {amount} NEAR from {a}"] }

open NearInterface in
/-- \cref{spec:deposit-available} for a call: `near_deposit` succeeds in the
model, and at the boundary it succeeds exactly when the account pays the
storage stake of the new state. -/
@[blueprint "spec:deposit-available-boundary"
  (statement := /-- Under the hypotheses of \cref{spec:deposit-available} for the context's predecessor and deposit, \texttt{near\_deposit} succeeds in the model with the properties stated there, and at the function-call boundary it has the same outcome unless the account cannot pay the storage stake of the new state, in which case it fails with that deficit. -/)]
def DepositAvailableAtBoundary : Prop :=
  ∀ (cfg : Config) (s : State) (ctx : Context),
    let env := Env.ofContext ctx
    Inv cfg s → 0 < ctx.attached → s.totalSupply + ctx.attached < u128Bound →
    (env.predecessor ∈ s.registered ∨ s.storageMin ≤ ctx.attached) →
    ∃ o, step (Config.ofRuntime ctx.protocol) (some s) env .nearDeposit = .ok o ∧
      env.predecessor ∈ o.state.registered ∧
      o.state.balance env.predecessor
        + (if env.predecessor ∈ s.registered then 0 else s.storageMin)
        = s.balance env.predecessor + ctx.attached ∧
      o.promises = [] ∧
      let deficit := stakeDeficit ctx.protocol (usageAfter ctx (some s) o.state)
        (ctx.balance + ctx.attached) ctx.locked
      contractStep ctx (some s) .nearDeposit =
        if 0 < deficit then .error { failure := .lackBalanceForState deficit, logs := o.logs }
        else .ok { state := o.state, ret := o.ret, logs := o.logs, promises := [] }

end WNear
