import Spec.Invariants

/-!
# Authorization

Nobody can move or unregister somebody else's wNEAR.
-/

namespace WNear

/-- In one execution with predecessor `P`, no account other than `P` loses
balance, except the receiver of an earlier `ft_transfer_call` inside the
contract's own `ft_resolve_transfer` callback, and then by at most the amount
of that transfer. -/
@[blueprint "spec:balance-authorization"
  (statement := /-- If an execution by predecessor $P$ succeeds and some account $a \ne P$ ends with a smaller balance, then the call was \texttt{ft\_resolve\_transfer}$(\_, a, \mathit{amount})$ and $a$ lost at most $\mathit{amount}$. -/)]
def BalanceAuthorization : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (call : Call) (o : Outcome),
    Inv cfg s → step cfg (some s) env call = .ok o →
    ∀ a, a ≠ env.predecessor → o.state.balance a < s.balance a →
      ∃ sender amount, call = .ftResolveTransfer sender a amount ∧
        s.balance a - o.state.balance a ≤ amount

/-- Only the predecessor itself can be unregistered. -/
@[blueprint "spec:registration-authorization"
  (statement := /-- If an execution by predecessor $P$ succeeds and an account registered before is not registered after, that account is $P$. -/)]
def RegistrationAuthorization : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (call : Call) (o : Outcome),
    Inv cfg s → step cfg (some s) env call = .ok o →
    ∀ a, a ∈ s.registered → a ∉ o.state.registered → a = env.predecessor

end WNear
