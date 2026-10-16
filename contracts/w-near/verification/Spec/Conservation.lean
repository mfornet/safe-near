import Spec.Invariants

/-!
# Conservation of NEAR

The NEAR the contract keeps in one execution covers the wNEAR it minted and
the registration fees it owes. Summed over a history this is the solvency of
`wrap.near`: its balance always covers the total supply plus one storage fee
per registered account (chain-level statement, see the blueprint).
-/

namespace WNear

/-- Per execution: minted supply plus newly collected registration fees never
exceed the attached deposit minus the NEAR sent out. Equality fails only where
NEAR is intentionally left in the contract: the 1 yoctoNEAR of `ft_transfer`,
forced unregistration with a positive balance, and the burn branch of
`ft_resolve_transfer`. -/
@[blueprint "spec:conservation"
  (statement := /-- If an execution with attached deposit $d$ succeeds, sends out $\mathit{out}$ yoctoNEAR through its promises, and changes the supply by $\Delta S$ and the number of registered accounts by $\Delta n$, then $\Delta S + \mathrm{storageMin} \cdot \Delta n \le d - \mathit{out}$ in $\mathbb{Z}$. -/)]
def Conservation : Prop :=
  ∀ (cfg : Config) (s : State) (env : Env) (call : Call) (o : Outcome),
    Inv cfg s → step cfg (some s) env call = .ok o →
    (o.state.totalSupply : ℤ) - s.totalSupply
      + s.storageMin * ((o.state.registered.card : ℤ) - s.registered.card)
      ≤ (env.attachedDeposit : ℤ) - o.nearOut

end WNear
