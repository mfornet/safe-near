import Model.Types

namespace Linkdrop

structure State where
  initialized : Bool
  accounts : Key → Option Nat

def empty : State := ⟨false, fun _ => none⟩

def State.set (s : State) (k : Key) (v : Option Nat) : State :=
  { s with accounts := fun j => if j = k then v else s.accounts j }

def State.WF (s : State) : Prop :=
  (∀ k n, s.accounts k = some n → n ≤ maxAmount) ∧
  (s.initialized = false → ∀ k, s.accounts k = none)

/-- Storage contains finitely many keys; functional accounts alone would allow
infinite support. Kept separate from numeric bounds for reusable local lemmas. -/
def State.Finite (s : State) : Prop :=
  ∃ keys : List Key, ∀ k, k ∉ keys → s.accounts k = none

structure Outcome where
  state : State
  receipts : List Receipt := []
  result : Return := .unit

end Linkdrop
