import Model

/-!
# State invariant

`Inv` is the property every reachable contract state satisfies. It is the
hypothesis of every other specification and the conclusion of
`InvPreserved`.
-/

namespace WNear

/-- Runtime parameters under which the measured storage usage fits a `u64`. -/
def Config.WF (cfg : Config) : Prop := cfg.measuredAccountStorageUsage < u64Bound

/-- The invariant of reachable states: representation bounds, the total
supply equals the sum of all balances, and the per-account storage usage is
the one measured at initialisation. -/
@[blueprint "def:inv"
  (statement := /-- $\mathrm{Inv}_{\mathit{cfg}}(s)$: $s$ is well formed (\cref{def:state-wf}), $\mathrm{supply}(s) = \mathit{totalSupply}$ and $\mathit{accountStorageUsage}$ is the value measured at initialisation under $\mathit{cfg}$. -/)]
structure Inv (cfg : Config) (s : State) : Prop extends s.WF where
  supply : s.supply = s.totalSupply
  usage : s.accountStorageUsage = cfg.measuredAccountStorageUsage

/-- Every execution, starting from an uninitialised account or from a state
satisfying the invariant, ends in a state satisfying the invariant. In
particular the total supply always equals the sum of all balances. -/
@[blueprint "spec:inv-preserved"
  (statement := /-- For every configuration with a representable storage usage, every optional state satisfying \cref{def:inv} when present, every context and call: if \cref{def:step} succeeds, the resulting state satisfies \cref{def:inv}. -/)]
def InvPreserved : Prop :=
  ∀ (cfg : Config) (st : Option State) (env : Env) (call : Call) (o : Outcome),
    cfg.WF → (∀ s, st = some s → Inv cfg s) →
    step cfg st env call = .ok o → Inv cfg o.state

end WNear
