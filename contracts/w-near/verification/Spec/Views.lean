import Spec.Invariants

/-!
# View methods and initialisation
-/

namespace WNear

/-- View methods change nothing and schedule nothing. -/
@[blueprint "spec:views-pure"
  (statement := /-- A successful view call returns the same state, no promises and no logs. -/)]
def ViewsPure : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (call : Call) (o : Outcome),
    call.isView = true → step cfg (some s) env call = .ok o →
    o.state = s ∧ o.promises = [] ∧ o.logs = []

/-- View methods never panic on an initialised contract. -/
@[blueprint "spec:views-total"
  (statement := /-- On an initialised contract, view calls never panic. -/)]
def ViewsTotal : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (call : Call),
    call.isView = true → ∃ o, step cfg (some s) env call = .ok o

/-- `ft_balance_of` reports the model balance (0 for unregistered accounts). -/
@[blueprint "spec:balance-of"
  (statement := /-- Under \cref{def:inv}, \texttt{ft\_balance\_of}$(a)$ returns $\mathit{balance}(a)$. -/)]
def BalanceOfCorrect : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (a : AccountId) (o : Outcome),
    Inv cfg s → step cfg (some s) env (.ftBalanceOf a) = .ok o →
    o.ret = .u128 (s.balance a)

/-- `ft_total_supply` reports the sum of all balances. -/
@[blueprint "spec:total-supply"
  (statement := /-- Under \cref{def:inv}, \texttt{ft\_total\_supply} returns $\mathrm{supply}(s)$, the sum of all balances. -/)]
def TotalSupplyCorrect : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (o : Outcome),
    Inv cfg s → step cfg (some s) env .ftTotalSupply = .ok o →
    o.ret = .u128 s.supply

/-- `new` cannot run twice, and nothing else runs before `new`. -/
@[blueprint "spec:init-once"
  (statement := /-- With no deposit, \texttt{new} on an initialised contract panics with \emph{already initialized}; every other method panics on an uninitialised contract. -/)]
def InitOnce : Prop :=
  (∀ (cfg : Config) (s : State) (env : Env),
    env.attachedDeposit = 0 → step cfg (some s) env .new = .error .alreadyInitialized) ∧
  (∀ (cfg : Config) (env : Env) (call : Call),
    call ≠ .new → ∃ p, step cfg none env call = .error p)

end WNear
