import NearVM.Run

namespace Wasm

/-- Only transfers and function-call deposits move funds into a promise.
Stake amounts are receiver-side targets, not deposits. -/
def PromiseAction.deposit : PromiseAction → Nat
  | .functionCall _ _ amount _ | .transfer amount => amount
  | _ => 0

end Wasm

namespace Wasm.Near

/-- A receipt valuation may depend on receiver and ordered actions. This covers
deposit backing and reserved execution/prepaid gas; dependency data is separate. -/
abbrev ReceiptValuation := List UInt8 → List PromiseAction → Nat

def receiptsValue (value : ReceiptValuation) (receipts : List ReceiptSpec) : Nat :=
  (receipts.map fun receipt => value receipt.receiverId receipt.actions).sum

def promiseValue (value : ReceiptValuation) : NearPromise → Nat
  | .batch account actions | .callback _ account actions => value account actions
  | .and _ | .yielded .. => 0

def promisesValue (value : ReceiptValuation) (promises : List NearPromise) : Nat :=
  (promises.map (promiseValue value)).sum

/-- One conversion carries the action valuation once. A joint adds handles,
not additional backing for its referenced receipts. -/
theorem ConvertsPromise.value {before after : PromiseGraph} {promise : NearPromise}
    (h : ConvertsPromise before promise after) (value : ReceiptValuation) :
    receiptsValue value after.receipts = receiptsValue value before.receipts + promiseValue value promise := by
  cases h <;> simp [receiptsValue, promiseValue, PromiseGraph.addReceipt, PromiseGraph.addJoint]

/-- Conversion preserves every receiver/action valuation through an arbitrary
ordered mixture of receipts, callbacks and repeated/nested/empty joins. -/
theorem ConvertsPromises.value {before after : PromiseGraph} {promises : List NearPromise}
    (h : ConvertsPromises before promises after) (value : ReceiptValuation) :
    receiptsValue value after.receipts = receiptsValue value before.receipts + promisesValue value promises := by
  induction h with
  | nil graph => simp [promisesValue]
  | cons head tail ih =>
    rw [ih, head.value value]
    simp [promisesValue, Nat.add_assoc]

/-- The executable converter preserves backing without assuming graph validity
or injectivity of dependency vectors. Unsupported conversion still returns none. -/
theorem convertPromises_value (promises : List NearPromise) (graph : PromiseGraph)
    (h : convertPromises promises = some graph) (value : ReceiptValuation) :
    receiptsValue value graph.receipts = promisesValue value promises := by
  have hv := (convertPromisesFrom_sound h).value value
  simpa [receiptsValue] using hv

def depositValue : ReceiptValuation := fun _ actions => (actions.map PromiseAction.deposit).sum

def receiptsDeposits (receipts : List ReceiptSpec) : Nat := receiptsValue depositValue receipts

def promisesDeposits (promises : List NearPromise) : Nat := promisesValue depositValue promises

theorem convertPromises_deposits (promises : List NearPromise) (graph : PromiseGraph)
    (h : convertPromises promises = some graph) :
    receiptsDeposits graph.receipts = promisesDeposits promises :=
  convertPromises_value promises graph h depositValue

/-- Replacing one element changes a mapped sum by the difference. -/
theorem map_sum_set {α : Type} (f : α → Nat) (l : List α) (i : Nat) (x y : α) (h : l[i]? = some x) :
    ((l.set i y).map f).sum + f x = (l.map f).sum + f y := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have := ih i h
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- A valuation that ignores the prepaid gas of function calls. -/
def GasInsensitive (value : ReceiptValuation) : Prop :=
  ∀ (g : Nat) (receiver : List UInt8) (actions : List PromiseAction) (i : Nat) (a a' : PromiseAction),
    actions[i]? = some a → a.addGas? g = some a' → value receiver (actions.set i a') = value receiver actions

theorem applyGasShare_value (value : ReceiptValuation) (hv : GasInsensitive value)
    (receipts : List ReceiptSpec) (receipt action g : Nat) :
    receiptsValue value (applyGasShare receipts receipt action g).1 = receiptsValue value receipts := by
  unfold applyGasShare
  split
  · rename_i spec hspec
    split
    · rename_i a ha
      split
      · rename_i a' hadd
        have := map_sum_set (fun r : ReceiptSpec => value r.receiverId r.actions) receipts receipt spec
          { spec with actions := spec.actions.set action a' } hspec
        have he := hv g spec.receiverId spec.actions action a a' ha hadd
        simp only [receiptsValue] at this ⊢
        rw [he] at this
        omega
      · rfl
    · rfl
  · rfl

theorem distributeStep_value (value : ReceiptValuation) (hv : GasInsensitive value)
    (unused total : Nat) (weights : List (Nat × Nat × Nat)) (handles : List PromiseHandle)
    (acc : List ReceiptSpec × Nat) (entry : (Nat × Nat × Nat) × Nat) :
    receiptsValue value (distributeStep unused total weights handles acc entry).1 = receiptsValue value acc.1 := by
  unfold distributeStep
  split
  · exact applyGasShare_value value hv _ _ _ _
  · rfl

theorem foldl_distributeStep_value (value : ReceiptValuation) (hv : GasInsensitive value)
    (unused total : Nat) (weights : List (Nat × Nat × Nat)) (handles : List PromiseHandle)
    (entries : List ((Nat × Nat × Nat) × Nat)) (acc : List ReceiptSpec × Nat) :
    receiptsValue value (entries.foldl (distributeStep unused total weights handles) acc).1 =
      receiptsValue value acc.1 := by
  induction entries generalizing acc with
  | nil => rfl
  | cons entry rest ih =>
    rw [List.foldl_cons, ih, distributeStep_value value hv]

/-- Distribution changes only function-call gas. -/
theorem distributeGas_value (value : ReceiptValuation) (hv : GasInsensitive value)
    (unused : Nat) (handles : List PromiseHandle) (weights : List (Nat × Nat × Nat))
    (receipts : List ReceiptSpec) :
    receiptsValue value (distributeGas unused handles weights receipts).1 = receiptsValue value receipts := by
  unfold distributeGas
  dsimp only
  split
  · rfl
  · exact foldl_distributeStep_value value hv _ _ _ _ _ _

theorem depositValue_gasInsensitive : GasInsensitive depositValue := by
  intro g receiver actions i a a' ha hadd
  have hd : a'.deposit = a.deposit := by
    cases a with
    | functionCall method args amount gas =>
      simp only [PromiseAction.addGas?] at hadd
      split at hadd
      · cases hadd; rfl
      · cases hadd
    | _ => simp [PromiseAction.addGas?] at hadd
  have := map_sum_set PromiseAction.deposit actions i a a' ha
  simp only [depositValue]
  omega

theorem distributeGas_deposits (unused : Nat) (handles : List PromiseHandle)
    (weights : List (Nat × Nat × Nat)) (receipts : List ReceiptSpec) :
    receiptsDeposits (distributeGas unused handles weights receipts).1 = receiptsDeposits receipts :=
  distributeGas_value depositValue depositValue_gasInsensitive unused handles weights receipts

/-- A successful executable VM result contains exactly the converted receipt
valuation. Graph errors cannot silently discard or manufacture backing. -/
theorem outcomeOfExecution_success_value (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : Machine) (error : Option FunctionCallError)
    (hsuccess : (outcomeOfExecution ctx storage final error).aborted = none) (value : ReceiptValuation)
    (hv : GasInsensitive value) :
    receiptsValue value (outcomeOfExecution ctx storage final error).receipts =
      promisesValue value final.host.promises := by
  unfold outcomeOfExecution at hsuccess ⊢
  dsimp only at hsuccess ⊢
  split at hsuccess
  · contradiction
  · cases hc : convertPromises final.host.promises with
    | none => simp [hc, VMOutcome.graphIssue] at hsuccess
    | some graph =>
      simp only [hc] at hsuccess ⊢
      split at hsuccess
      · simp [VMOutcome.graphIssue] at hsuccess
      · rw [distributeGas_value value hv]
        exact convertPromises_value _ graph hc value

/-- Replacing one raw handle changes only that handle's valuation. -/
theorem setPromise_value (value : ReceiptValuation) (promises result : List NearPromise)
    (index : Nat) (old replacement : NearPromise)
    (hget : getPromise? promises index = some old)
    (hset : setPromise? promises index replacement = some result) :
    promisesValue value result + promiseValue value old =
      promisesValue value promises + promiseValue value replacement := by
  induction promises generalizing index result with
  | nil => simp [getPromise?] at hget
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [getPromise?, Option.some.injEq] at hget
      subst old
      simp only [setPromise?, Option.some.injEq] at hset
      subst result
      simp only [promisesValue, List.map_cons, List.sum_cons]
      omega
    | succ index =>
      obtain ⟨rest, hrest, heq⟩ := Option.map_eq_some_iff.mp hset
      subst result
      have ht := ih rest index hget hrest
      simp only [promisesValue, List.map_cons, List.sum_cons] at ht ⊢
      omega

/-- Appending a funded action increases raw promise backing by its deposit,
without changing the backing of other promises or duplicating a callback. -/
theorem appendPromiseAction_deposits (promises result : List NearPromise) (index : Nat)
    (action : PromiseAction) (h : appendPromiseAction? promises index action = some result) :
    promisesDeposits result = promisesDeposits promises + action.deposit := by
  unfold appendPromiseAction? at h
  cases hg : getPromise? promises index with
  | none => simp [hg] at h
  | some promise =>
    cases promise with
    | batch account actions =>
      have hs : setPromise? promises index (.batch account (actions ++ [action])) = some result := by
        simpa only [hg] using h
      have hv := setPromise_value depositValue promises result index (.batch account actions)
        (.batch account (actions ++ [action])) hg hs
      have hn : promiseValue depositValue (.batch account (actions ++ [action])) =
          promiseValue depositValue (.batch account actions) + action.deposit := by
        simp [promiseValue, depositValue]
      rw [hn] at hv
      change promisesValue depositValue result = promisesValue depositValue promises + action.deposit
      omega
    | callback base account actions =>
      have hs : setPromise? promises index (.callback base account (actions ++ [action])) = some result := by
        simpa only [hg] using h
      have hv := setPromise_value depositValue promises result index (.callback base account actions)
        (.callback base account (actions ++ [action])) hg hs
      have hn : promiseValue depositValue (.callback base account (actions ++ [action])) =
          promiseValue depositValue (.callback base account actions) + action.deposit := by
        simp [promiseValue, depositValue]
      rw [hn] at hv
      change promisesValue depositValue result = promisesValue depositValue promises + action.deposit
      omega
    | and dependencies => simp [hg] at h
    | yielded => simp [hg] at h

/-- Creating a raw receipt funds it once; empty batches and joints add zero
attached deposits. -/
theorem appendPromise_deposits (st : HostStore NearState) (promise : NearPromise) :
    promisesDeposits (appendPromise st promise).host.promises =
      promisesDeposits st.host.promises + promiseValue depositValue promise := by
  simp [appendPromise, promisesDeposits, promisesValue]

/-- Deposit charging changes neither the raw promises nor their asset backing. -/
@[simp] theorem deductPromiseDeposit_promises (name : String) (ns : NearState) (amount : Nat) :
    (deductPromiseDeposit name ns amount).1.promises = ns.promises := by
  unfold deductPromiseDeposit
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- The financial charge at the actual host ABI seam accounts for the exact
memory-decoded deposit and any one-yocto subsidy, on every successful exit. -/
theorem deductDeposit_accounting (name : String) (before after : HostStore NearState) (args : List Value)
    (hsuccess : (deductDeposit name before after args).2 = none) :
    let paid := (deductDeposit name before after args).1.host
    after.host.context.accountBalance + paid.subsidizedAmount =
      paid.context.accountBalance + after.host.subsidizedAmount + (promiseDeposit? name before args).getD 0 := by
  unfold deductDeposit at hsuccess ⊢
  cases hd : promiseDeposit? name before args with
  | none => simp
  | some amount =>
    cases amount with
    | zero => simp
    | succ amount =>
      have hp := deductPromiseDeposit_accounting name after.host (amount + 1)
      simp only [hd] at hsuccess ⊢
      exact hp hsuccess

/-- Appending a promise action and successfully charging its attached deposit
conserves liquid funds plus promise backing, with subsidies explicit. -/
theorem appendPromiseAction_funded (name : String) (ns : NearState) (index : Nat) (action : PromiseAction)
    (promises : List NearPromise) (happend : appendPromiseAction? ns.promises index action = some promises)
    (hpaid : (deductPromiseDeposit name { ns with promises } action.deposit).2 = none) :
    let paid := (deductPromiseDeposit name { ns with promises } action.deposit).1
    paid.context.accountBalance + promisesDeposits paid.promises + ns.subsidizedAmount =
      ns.context.accountBalance + promisesDeposits ns.promises + paid.subsidizedAmount := by
  have ha := appendPromiseAction_deposits ns.promises promises index action happend
  have hp := deductPromiseDeposit_accounting name { ns with promises } action.deposit hpaid
  dsimp only at hp ⊢
  rw [deductPromiseDeposit_promises]
  change _ + promisesDeposits promises + _ = _
  omega

end Wasm.Near
