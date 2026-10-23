import NearVM.PromiseGraph

/-!
# Distribution of unused gas to weighted function calls

nearcore's `ReceiptManager::distribute_gas` (`runtime/runtime/src/receipt_manager.rs`),
called by `function_call.rs` after the VM returns: the unused prepaid gas
`prepaid - used` is split among the weighted function-call actions in the
order they were added, each receiving `unused * weight / total`, the last one
also the rounding remainder; the call's used gas grows by what was split.

nearcore panics on a weight whose action is not a function call and fails on
a `u64` overflow. Neither can happen: weights are recorded on the function
call just appended, and every action's gas is part of the used gas, which with
the unused gas makes at most the prepaid `u64`. The model adds a share only
where it applies and counts exactly the gas it added, so the used gas stays
the burnt gas plus the receipts' gas by construction.
-/

namespace Wasm.Near

/-- `checked_add` of a share to a function call's prepaid gas. -/
def _root_.Wasm.PromiseAction.addGas? (g : Nat) : PromiseAction → Option PromiseAction
  | .functionCall method args amount gas =>
    if gas.toNat + g < 2 ^ 64 then some (.functionCall method args amount (UInt64.ofNat (gas.toNat + g)))
    else none
  | _ => none

/-- Add `g` to action `action` of receipt `receipt`; returns the gas added. -/
def applyGasShare (receipts : List ReceiptSpec) (receipt action g : Nat) : List ReceiptSpec × Nat :=
  match receipts[receipt]? with
  | some spec =>
    match spec.actions[action]? with
    | some a =>
      match a.addGas? g with
      | some a' => (receipts.set receipt { spec with actions := spec.actions.set action a' }, g)
      | none => (receipts, 0)
    | none => (receipts, 0)
  | none => (receipts, 0)

def gasWeightTotal (weights : List (Nat × Nat × Nat)) : Nat :=
  (weights.map fun w => w.2.2).sum

/-- Share of entry `i` with weight `w`; the last entry also takes the remainder. -/
def gasShare (unused total : Nat) (weights : List (Nat × Nat × Nat)) (i w : Nat) : Nat :=
  unused * w / total +
    (if i + 1 = weights.length then unused - (weights.map fun x => unused * x.2.2 / total).sum else 0)

/-- One step: locate the receipt through the promise handle and add the share. -/
def distributeStep (unused total : Nat) (weights : List (Nat × Nat × Nat)) (handles : List PromiseHandle)
    (acc : List ReceiptSpec × Nat) (entry : (Nat × Nat × Nat) × Nat) : List ReceiptSpec × Nat :=
  match handles[entry.1.1]? with
  | some (.receipt receipt) =>
    let r := applyGasShare acc.1 receipt entry.1.2.1 (gasShare unused total weights entry.2 entry.1.2.2)
    (r.1, acc.2 + r.2)
  | _ => acc

/-- The receipts after distribution and the gas distributed. -/
def distributeGas (unused : Nat) (handles : List PromiseHandle) (weights : List (Nat × Nat × Nat))
    (receipts : List ReceiptSpec) : List ReceiptSpec × Nat :=
  let total := gasWeightTotal weights
  if total = 0 ∨ unused = 0 then (receipts, 0)
  else weights.zipIdx.foldl (distributeStep unused total weights handles) (receipts, 0)

@[simp] theorem distributeGas_nil (unused : Nat) (handles : List PromiseHandle) (receipts : List ReceiptSpec) :
    distributeGas unused handles [] receipts = (receipts, 0) := by
  simp [distributeGas, gasWeightTotal]

/-! ## The distributed gas is at most the unused gas -/

theorem applyGasShare_le (receipts : List ReceiptSpec) (receipt action g : Nat) :
    (applyGasShare receipts receipt action g).2 ≤ g := by
  unfold applyGasShare
  repeat' split
  all_goals simp

theorem distributeStep_le (unused total : Nat) (weights : List (Nat × Nat × Nat))
    (handles : List PromiseHandle) (acc : List ReceiptSpec × Nat) (entry : (Nat × Nat × Nat) × Nat) :
    (distributeStep unused total weights handles acc entry).2 ≤
      acc.2 + gasShare unused total weights entry.2 entry.1.2.2 := by
  unfold distributeStep
  split
  · rename_i receipt _
    have := applyGasShare_le acc.1 receipt entry.1.2.1 (gasShare unused total weights entry.2 entry.1.2.2)
    dsimp only
    omega
  · omega

theorem foldl_distributeStep_le (unused total : Nat) (weights : List (Nat × Nat × Nat))
    (handles : List PromiseHandle) (entries : List ((Nat × Nat × Nat) × Nat)) (acc : List ReceiptSpec × Nat) :
    (entries.foldl (distributeStep unused total weights handles) acc).2 ≤
      acc.2 + (entries.map fun e => gasShare unused total weights e.2 e.1.2.2).sum := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry rest ih =>
    rw [List.foldl_cons]
    have h1 := ih (distributeStep unused total weights handles acc entry)
    have h2 := distributeStep_le unused total weights handles acc entry
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_zipIdx_shares {α : Type} (f : α → Nat) (R n : Nat) (l : List α) (k : Nat)
    (hn : n = k + l.length) :
    ((l.zipIdx k).map fun e => f e.1 + (if e.2 + 1 = n then R else 0)).sum =
      (l.map f).sum + (if l = [] then 0 else R) := by
  induction l generalizing k with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (k + 1) (by simp at hn; omega)]
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hn ⊢
    cases xs with
    | nil => simp [hn]
    | cons y ys =>
      have : ¬ k + 1 = n := by simp at hn; omega
      simp [this]
      omega

private theorem sum_div_le {α : Type} (a : α → Nat) (T : Nat) (hT : 0 < T) (l : List α) :
    (l.map fun x => a x / T).sum ≤ (l.map a).sum / T := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    apply (Nat.le_div_iff_mul_le hT).mpr
    have h1 := Nat.div_mul_le_self (a x) T
    have h2 := (Nat.le_div_iff_mul_le hT).mp ih
    have h3 := Nat.div_mul_le_self ((xs.map a).sum) T
    rw [Nat.add_mul]
    omega

private theorem sum_mul_left {α : Type} (u : Nat) (w : α → Nat) (l : List α) :
    (l.map fun x => u * w x).sum = u * (l.map w).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- nearcore asserts that exactly the unused gas is distributed; the model's
count of applied shares is at most that. -/
theorem distributeGas_le (unused : Nat) (handles : List PromiseHandle) (weights : List (Nat × Nat × Nat))
    (receipts : List ReceiptSpec) : (distributeGas unused handles weights receipts).2 ≤ unused := by
  unfold distributeGas
  dsimp only
  split
  · simp
  · rename_i hne
    have hT : 0 < gasWeightTotal weights := by omega
    have hf := foldl_distributeStep_le unused (gasWeightTotal weights) weights handles weights.zipIdx (receipts, 0)
    have hs := sum_zipIdx_shares (fun x : Nat × Nat × Nat => unused * x.2.2 / gasWeightTotal weights)
      (unused - (weights.map fun x => unused * x.2.2 / gasWeightTotal weights).sum) weights.length weights 0
      (by simp)
    have hfl := sum_div_le (fun x : Nat × Nat × Nat => unused * x.2.2) (gasWeightTotal weights) hT weights
    rw [sum_mul_left, ← gasWeightTotal, Nat.mul_div_cancel _ hT] at hfl
    simp only [gasShare] at hf
    rw [hs] at hf
    split at hf <;> omega

end Wasm.Near
