import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Spec.Invariants

/-!
# Lemmas about the state operations

How `setBalance`, `register`, `unregister`, `deposit`, `withdraw` and
`registerAccount` act on `supply`, `registered` and the well-formedness
bounds. Used by every preservation proof.
-/

namespace WNear

open Finset

@[simp] theorem throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl
@[simp] theorem ok_bind {α β : Type} (a : α) (k : α → M β) : (Except.ok a >>= k) = k a := rfl
@[simp] theorem error_bind {α β : Type} (p : Panic) (k : α → M β) :
    (Except.error p >>= k) = Except.error p := rfl
@[simp] theorem pure_eq_ok {α : Type} (a : α) : (pure a : M α) = Except.ok a := rfl

@[simp] theorem require_bind {α : Type} {c : Prop} [Decidable c] {p : Panic} {k : Unit → M α} :
    (require c p >>= k) = if c then k () else .error p := by
  unfold require; split <;> rfl

@[simp] theorem bind_require {α : Type} {c : Prop} [Decidable c] {p : Panic} {k : Unit → M α} :
    Except.bind (require c p) k = if c then k () else .error p := by
  unfold require; split <;> rfl

@[simp] theorem bind_ok' {α β : Type} (a : α) (k : α → M β) : Except.bind (Except.ok a) k = k a := rfl
@[simp] theorem bind_error' {α β : Type} (p : Panic) (k : α → M β) :
    Except.bind (Except.error p) k = Except.error p := rfl

@[simp] theorem require_eq_ok {c : Prop} [Decidable c] {p : Panic} :
    (require c p = .ok ()) ↔ c := by
  unfold require; split <;> simp_all

namespace State

@[simp] theorem setBalance_registered (s : State) (a : AccountId) (b : Nat) :
    (s.setBalance a b).registered = s.registered := rfl
@[simp] theorem setBalance_totalSupply (s : State) (a : AccountId) (b : Nat) :
    (s.setBalance a b).totalSupply = s.totalSupply := rfl
@[simp] theorem setBalance_usage (s : State) (a : AccountId) (b : Nat) :
    (s.setBalance a b).accountStorageUsage = s.accountStorageUsage := rfl
@[simp] theorem setBalance_balance (s : State) (a : AccountId) (b : Nat) :
    (s.setBalance a b).balance = Function.update s.balance a b := rfl

@[simp] theorem register_registered (s : State) (a : AccountId) :
    (s.register a).registered = insert a s.registered := rfl
@[simp] theorem register_totalSupply (s : State) (a : AccountId) :
    (s.register a).totalSupply = s.totalSupply := rfl
@[simp] theorem register_usage (s : State) (a : AccountId) :
    (s.register a).accountStorageUsage = s.accountStorageUsage := rfl
@[simp] theorem register_balance (s : State) (a : AccountId) :
    (s.register a).balance = Function.update s.balance a 0 := rfl

@[simp] theorem unregister_registered (s : State) (a : AccountId) :
    (s.unregister a).registered = s.registered.erase a := rfl
@[simp] theorem unregister_totalSupply (s : State) (a : AccountId) :
    (s.unregister a).totalSupply = s.totalSupply := rfl
@[simp] theorem unregister_usage (s : State) (a : AccountId) :
    (s.unregister a).accountStorageUsage = s.accountStorageUsage := rfl
@[simp] theorem unregister_balance (s : State) (a : AccountId) :
    (s.unregister a).balance = Function.update s.balance a 0 := rfl

/-- Changing the balance of a registered account shifts the supply by the difference. -/
theorem supply_setBalance_of_mem {s : State} {a : AccountId} (h : a ∈ s.registered) (b : Nat) :
    (s.setBalance a b).supply + s.balance a = s.supply + b := by
  unfold supply
  simp only [setBalance_registered, setBalance_balance]
  rw [Finset.sum_update_of_mem h, Finset.sdiff_singleton_eq_erase,
    ← Finset.sum_erase_add _ _ h]
  omega

/-- Registering a new account with balance `0` does not change the supply. -/
theorem supply_register_of_not_mem {s : State} {a : AccountId} (h : a ∉ s.registered) :
    (s.register a).supply = s.supply := by
  unfold supply
  simp only [register_registered, register_balance]
  rw [Finset.sum_insert h, Function.update_self, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Function.update_of_ne]
  rintro rfl
  exact h hx

/-- Unregistering an account removes its balance from the supply. -/
theorem supply_unregister_of_mem {s : State} {a : AccountId} (h : a ∈ s.registered) :
    (s.unregister a).supply + s.balance a = s.supply := by
  unfold supply
  simp only [unregister_registered, unregister_balance]
  rw [← Finset.sum_erase_add _ _ h]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]

/-- A registered balance is at most the supply. -/
theorem balance_le_supply {s : State} {a : AccountId} (h : a ∈ s.registered) :
    s.balance a ≤ s.supply :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) h

theorem WF.setBalance {s : State} (hs : s.WF) {a : AccountId} (ha : a ∈ s.registered) {b : Nat}
    (hb : b < u128Bound) : (s.setBalance a b).WF where
  unregistered_zero x hx := by
    simp only [setBalance_registered] at hx
    simp only [setBalance_balance]
    rw [Function.update_of_ne (fun h => hx (by rw [h]; exact ha))]
    exact hs.unregistered_zero x hx
  balance_lt x := by
    simp only [setBalance_balance]
    by_cases hxa : x = a
    · subst hxa; simp [hb]
    · rw [Function.update_of_ne hxa]; exact hs.balance_lt x
  totalSupply_lt := hs.totalSupply_lt
  usage_lt := hs.usage_lt

theorem WF.register {s : State} (hs : s.WF) (a : AccountId) : (s.register a).WF where
  unregistered_zero x hx := by
    simp only [register_registered, Finset.mem_insert, not_or] at hx
    simp only [register_balance]
    rw [Function.update_of_ne hx.1]
    exact hs.unregistered_zero x hx.2
  balance_lt x := by
    simp only [register_balance]
    by_cases hxa : x = a
    · subst hxa; simp [u128Bound]
    · rw [Function.update_of_ne hxa]; exact hs.balance_lt x
  totalSupply_lt := hs.totalSupply_lt
  usage_lt := hs.usage_lt

theorem WF.unregister {s : State} (hs : s.WF) (a : AccountId) : (s.unregister a).WF where
  unregistered_zero x hx := by
    simp only [unregister_registered, Finset.mem_erase, not_and'] at hx
    simp only [unregister_balance]
    by_cases hxa : x = a
    · subst hxa; simp
    · rw [Function.update_of_ne hxa]; exact hs.unregistered_zero x (fun hm => (hx hm hxa).elim)
  balance_lt x := by
    simp only [unregister_balance]
    by_cases hxa : x = a
    · subst hxa; simp [u128Bound]
    · rw [Function.update_of_ne hxa]; exact hs.balance_lt x
  totalSupply_lt := hs.totalSupply_lt
  usage_lt := hs.usage_lt

theorem WF.withTotalSupply {s : State} (hs : s.WF) {t : Nat} (ht : t < u128Bound) :
    ({ s with totalSupply := t } : State).WF where
  unregistered_zero := hs.unregistered_zero
  balance_lt := hs.balance_lt
  totalSupply_lt := ht
  usage_lt := hs.usage_lt

/-- Characterisation of a successful `deposit`. -/
theorem deposit_ok {s : State} {a : AccountId} {amount : Nat} {s' : State} :
    s.deposit a amount = .ok s' ↔
      a ∈ s.registered ∧ s.balance a + amount < u128Bound ∧ s.totalSupply + amount < u128Bound ∧
      s' = { s.setBalance a (s.balance a + amount) with totalSupply := s.totalSupply + amount } := by
  unfold deposit unwrapBalance
  simp only [bind, bind_require, pure_eq_ok]
  by_cases h0 : a ∈ s.registered <;>
    by_cases h1 : s.balance a + amount < u128Bound <;>
    by_cases h2 : s.totalSupply + amount < u128Bound <;>
    simp [h0, h1, h2, eq_comm]

/-- Characterisation of a successful `withdraw`. -/
theorem withdraw_ok {s : State} {a : AccountId} {amount : Nat} {s' : State} :
    s.withdraw a amount = .ok s' ↔
      a ∈ s.registered ∧ amount ≤ s.balance a ∧ amount ≤ s.totalSupply ∧
      s' = { s.setBalance a (s.balance a - amount) with totalSupply := s.totalSupply - amount } := by
  unfold withdraw unwrapBalance
  simp only [bind, bind_require, pure_eq_ok]
  by_cases h0 : a ∈ s.registered <;>
    by_cases h1 : amount ≤ s.balance a <;>
    by_cases h2 : amount ≤ s.totalSupply <;>
    simp [h0, h1, h2, eq_comm]

/-- Characterisation of a successful `registerAccount`. -/
theorem registerAccount_ok {s : State} {a : AccountId} {s' : State} :
    s.registerAccount a = .ok s' ↔ a ∉ s.registered ∧ s' = s.register a := by
  unfold registerAccount
  simp only [bind, bind_require, pure_eq_ok]
  split_ifs <;> simp_all [eq_comm]

end State

end WNear

namespace WNear

/-- Monadic case analysis: a bind succeeds iff both halves succeed. -/
theorem bind_ok_iff {α β : Type} {x : M α} {k : α → M β} {b : β} :
    Except.bind x k = .ok b ↔ ∃ a, x = .ok a ∧ k a = .ok b := by
  cases x <;> simp [Except.bind]

/-- A bind whose continuation always fails cannot succeed. -/
theorem bind_const_error {α β : Type} {x : M α} {p : Panic} {b : β}
    (h : Except.bind x (fun _ => Except.error p) = .ok b) : False := by
  cases x <;> simp [Except.bind] at h

@[simp] theorem bind_ite {α β : Type} {c : Prop} [Decidable c] {x y : M α} {k : α → M β} :
    Except.bind (if c then x else y) k = if c then Except.bind x k else Except.bind y k := by
  split <;> rfl

@[simp] theorem supply_withTotalSupply (s : State) (t : Nat) :
    ({ s with totalSupply := t } : State).supply = s.supply := rfl

@[simp] theorem registered_withTotalSupply (s : State) (t : Nat) :
    ({ s with totalSupply := t } : State).registered = s.registered := rfl

@[simp] theorem usage_withTotalSupply (s : State) (t : Nat) :
    ({ s with totalSupply := t } : State).accountStorageUsage = s.accountStorageUsage := rfl

@[simp] theorem balance_withTotalSupply (s : State) (t : Nat) :
    ({ s with totalSupply := t } : State).balance = s.balance := rfl

theorem State.balanceOf_pos_mem {s : State} {a : AccountId} (h : 0 < s.balanceOf a) :
    a ∈ s.registered ∧ s.balanceOf a = s.balance a := by
  by_cases hm : a ∈ s.registered
  · exact ⟨hm, by simp [State.balanceOf, hm]⟩
  · simp [State.balanceOf, hm] at h

end WNear
