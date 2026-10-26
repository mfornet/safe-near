/-!
# NEP-145 storage management, as an environment contract

What a contract may assume about the storage registration of a NEP-145
contract it calls, on what callers can observe: `storage_balance_of` and
`storage_balance_bounds`.
-/

namespace NearSdk.Nep145

variable {α : Type} [DecidableEq α]

/-- `StorageBalance`. -/
structure Balance where
  total : Nat
  available : Nat
  deriving DecidableEq, Repr

/-- What callers observe: each account's storage balance (`none` when unregistered) and the
bounds. -/
structure View (α : Type) where
  balanceOf : α → Option Balance
  min : Nat
  max : Option Nat

def View.registered (v : View α) (a : α) : Bool := (v.balanceOf a).isSome

/-- A successful `storage_deposit(account)` with `deposit` attached. An already registered
account changes nothing (the deposit is refunded or credited per contract); a new one must
pay at least `min` and is registered afterwards; no other account changes. -/
structure Deposit (v v' : View α) (account : α) (deposit : Nat) : Prop where
  covered : v.registered account = false → v.min ≤ deposit
  registered : v'.registered account = true
  others : ∀ a, a ≠ account → v'.balanceOf a = v.balanceOf a
  bounds : v'.min = v.min ∧ v'.max = v.max

end NearSdk.Nep145
