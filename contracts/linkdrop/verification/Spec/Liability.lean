import Spec.Economics

namespace Linkdrop.Spec

/-- Sum over a finite, duplicate-free universe of keys containing the entry being
changed. Callers may choose a superset of all stored keys; missing keys weigh zero. -/
def liability (s : State) (keys : List Key) : Nat :=
  (keys.map fun k => (s.accounts k).getD 0).sum

/-- Deposit cannot create more aggregate key liabilities than it receives. -/
def SendConservation : Prop :=
  ∀ s e k out keys, keys.Nodup → k ∈ keys →
    step s e (.send k) = .ok out →
    liability out.state keys ≤ liability s keys + e.deposit

/-- Claim consumes exactly its scheduled payout from aggregate map liabilities.
This concerns scheduling; a later failed payout has no resolver. -/
def ClaimConservation : Prop :=
  ∀ s e account amount out keys, keys.Nodup → e.signerKey ∈ keys →
    s.accounts e.signerKey = some amount → step s e (.claim account) = .ok out →
    liability out.state keys + amount = liability s keys

/-- Restoring a pending amount conserves (map + pending) liability only when the
key is still absent. The interference counterexample shows why this matters. -/
def RestoreConservation : Prop :=
  ∀ (s : State) (e : Env) amount keys, keys.Nodup → e.signerKey ∈ keys →
    s.accounts e.signerKey = none →
    liability (s.set e.signerKey (some amount)) keys = liability s keys + amount

end Linkdrop.Spec
