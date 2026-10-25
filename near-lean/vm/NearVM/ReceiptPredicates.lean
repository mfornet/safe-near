import NearVM.PromiseAccounting

namespace Wasm.Near

/-- A property of the receiver and ordered actions of a materialized receipt. -/
abbrev ReceiptPredicate := List UInt8 → List PromiseAction → Prop

/-- Joins create no receipt; every other handle is a receipt whose actions must satisfy it. -/
def PromiseSatisfies (property : ReceiptPredicate) : NearPromise → Prop
  | .batch receiver actions | .callback _ receiver actions | .yielded receiver actions _ =>
    property receiver actions
  | .and _ => True

private def violationValue (property : ReceiptPredicate) [DecidableRel property] : ReceiptValuation :=
  fun receiver actions => if property receiver actions then 0 else 1

private theorem promisesValue_zero (property : ReceiptPredicate) [DecidableRel property]
    (promises : List NearPromise) (h : ∀ promise ∈ promises, PromiseSatisfies property promise) :
    promisesValue (violationValue property) promises = 0 := by
  induction promises with
  | nil => rfl
  | cons head tail ih =>
    have hh := h head (by simp)
    have ht := ih (by intro p hp; exact h p (by simp [hp]))
    have hv : promiseValue (violationValue property) head = 0 := by
      cases head <;> simp_all [PromiseSatisfies, promiseValue, violationValue]
    simpa only [promisesValue, List.map_cons, List.sum_cons, hv, Nat.zero_add] using ht

private theorem receiptsValue_zero (property : ReceiptPredicate) [DecidableRel property]
    (receipts : List ReceiptSpec) (h : receiptsValue (violationValue property) receipts = 0) :
    ∀ receipt ∈ receipts, property receipt.receiverId receipt.actions := by
  induction receipts with
  | nil => simp
  | cons head tail ih =>
    change violationValue property head.receiverId head.actions +
      receiptsValue (violationValue property) tail = 0 at h
    have hh : violationValue property head.receiverId head.actions = 0 := by omega
    have ht : receiptsValue (violationValue property) tail = 0 := by omega
    have hp : property head.receiverId head.actions := by
      by_contra hn
      simp [violationValue, hn] at hh
    intro receipt hm
    rcases List.mem_cons.mp hm with he | he
    · subst receipt; exact hp
    · exact ih ht receipt he

/-- Updating one handle preserves the invariant when its replacement satisfies
it. The premise refers to the actual executable lookup and update. -/
theorem setPromise_preserves_predicate (property : ReceiptPredicate) [DecidableRel property]
    (promises result : List NearPromise) (index : Nat) (old replacement : NearPromise)
    (hget : getPromise? promises index = some old)
    (hset : setPromise? promises index replacement = some result)
    (h : ∀ promise ∈ promises, PromiseSatisfies property promise)
    (hreplacement : PromiseSatisfies property replacement) :
    ∀ promise ∈ result, PromiseSatisfies property promise := by
  induction promises generalizing index result with
  | nil => simp [getPromise?] at hget
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [setPromise?, Option.some.injEq] at hset
      subst result
      intro promise hm
      rcases List.mem_cons.mp hm with he | he
      · subst promise; exact hreplacement
      · exact h promise (List.mem_cons_of_mem head he)
    | succ index =>
      obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hset
      subst result
      have ht := ih rest index hget hrest
        (by intro promise hm; exact h promise (List.mem_cons_of_mem head hm))
      intro promise hm
      rcases List.mem_cons.mp hm with he | he
      · subst promise; exact h head (by simp)
      · exact ht promise he

/-- Successful executable conversion transports any decidable receiver/action
property, including through repeated, nested and empty joins. -/
theorem convertPromises_preserves_predicate (property : ReceiptPredicate) [DecidableRel property]
    (promises : List NearPromise) (graph : PromiseGraph)
    (hconvert : convertPromises promises = some graph)
    (h : ∀ promise ∈ promises, PromiseSatisfies property promise) :
    ∀ receipt ∈ graph.receipts, property receipt.receiverId receipt.actions := by
  apply receiptsValue_zero property
  rw [convertPromises_value promises graph hconvert, promisesValue_zero property promises h]

/-- A predicate that ignores the prepaid gas of function calls. -/
def PredicateGasInsensitive (property : ReceiptPredicate) : Prop :=
  ∀ (g : Nat) (receiver : List UInt8) (actions : List PromiseAction) (i : Nat) (a a' : PromiseAction),
    actions[i]? = some a → a.addGas? g = some a' → (property receiver (actions.set i a') ↔ property receiver actions)

private theorem violationValue_gasInsensitive (property : ReceiptPredicate) [DecidableRel property]
    (h : PredicateGasInsensitive property) : GasInsensitive (violationValue property) := by
  intro g receiver actions i a a' ha hadd
  simp only [violationValue, h g receiver actions i a a' ha hadd]

/-- Outcome packing preserves a final raw-promise invariant. Establishing that
invariant from concrete execution remains a separate proof obligation. -/
theorem outcomeOfExecution_success_predicate (property : ReceiptPredicate) [DecidableRel property]
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (final : Machine)
    (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none)
    (hgas : PredicateGasInsensitive property)
    (h : ∀ promise ∈ final.host.promises, PromiseSatisfies property promise) :
    ∀ receipt ∈ (outcomeOfExecution ctx storage final error).receipts,
      property receipt.receiverId receipt.actions := by
  apply receiptsValue_zero property
  rw [outcomeOfExecution_success_value ctx storage final error hsuccess _
      (violationValue_gasInsensitive property hgas),
    promisesValue_zero property _ h]

end Wasm.Near
