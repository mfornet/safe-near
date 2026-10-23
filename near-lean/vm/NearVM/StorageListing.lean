import NearVM.Run

/-!
# The VM does not depend on how storage is listed

The VM takes contract storage as a list; contract storage is a set of records
with one value per key. Two listings of the same records give the same
initial host state: lookups only see membership, and the key list is sorted.
-/

namespace Wasm.Near

/-- Each key has at most one value. -/
def KeysUnique (storage : List (Bytes × Bytes)) : Prop :=
  ∀ k v v', (k, v) ∈ storage → (k, v') ∈ storage → v = v'

theorem sortedKeys_perm {s₁ s₂ : List (Bytes × Bytes)} (h : s₁.Perm s₂) :
    sortedKeys s₁ = sortedKeys s₂ := by
  unfold sortedKeys
  have trans : ∀ a b c : Bytes, decide (a ≤ b) → decide (b ≤ c) → decide (a ≤ c) := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    exact List.le_trans hab hbc
  have total : ∀ a b : Bytes, (decide (a ≤ b) || decide (b ≤ a)) := by
    intro a b
    rcases List.le_total a b with hab | hba
    · simp [hab]
    · simp [hba]
  apply List.Perm.eq_of_pairwise _ (List.pairwise_mergeSort trans total _)
    (List.pairwise_mergeSort trans total _)
  · exact (List.mergeSort_perm _ _).trans ((h.map _).trans (List.mergeSort_perm _ _).symm)
  · intro a b _ _ hab hba
    simp only [decide_eq_true_eq] at hab hba
    exact List.le_antisymm hab hba

/-- With one value per key, a lookup finds the record of that key. -/
theorem find?_key_of_mem {s : List (Bytes × Bytes)} (hu : KeysUnique s) {k v : Bytes}
    (hm : (k, v) ∈ s) : (s.find? (·.1 == k)).map (·.2) = some v := by
  cases hf : s.find? (·.1 == k) with
  | none =>
    have := List.find?_eq_none.mp hf (k, v) hm
    simp at this
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    obtain ⟨k', v'⟩ := r
    simp only at hk
    subst hk
    simp only [Option.map_some, Option.some.injEq]
    exact hu _ _ _ hr hm

theorem find?_key_none {s : List (Bytes × Bytes)} {k : Bytes} (h : ∀ v, (k, v) ∉ s) :
    (s.find? (·.1 == k)).map (·.2) = none := by
  cases hf : s.find? (·.1 == k) with
  | none => rfl
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [beq_iff_eq] at hk
    obtain ⟨k', v'⟩ := r
    simp only at hk
    subst hk
    exact absurd hr (h v')

theorem lookup_perm {s₁ s₂ : List (Bytes × Bytes)} (h : s₁.Perm s₂) (hu : KeysUnique s₁) :
    (fun k => (s₁.find? (·.1 == k)).map (·.2)) = (fun k => (s₂.find? (·.1 == k)).map (·.2)) := by
  have hu₂ : KeysUnique s₂ := fun k v v' hv hv' => hu k v v' (h.mem_iff.mpr hv) (h.mem_iff.mpr hv')
  funext k
  by_cases hk : ∃ v, (k, v) ∈ s₁
  · obtain ⟨v, hv⟩ := hk
    rw [find?_key_of_mem hu hv, find?_key_of_mem hu₂ (h.mem_iff.mp hv)]
  · have h₁ : ∀ v, (k, v) ∉ s₁ := fun v hv => hk ⟨v, hv⟩
    have h₂ : ∀ v, (k, v) ∉ s₂ := fun v hv => h₁ v (h.mem_iff.mpr hv)
    rw [find?_key_none h₁, find?_key_none h₂]

/-- Two listings of the same records give the same initial host state. -/
theorem toNearState_perm (cfg : RuntimeConfig) (ctx : VMContext) {s₁ s₂ : List (Bytes × Bytes)}
    (h : s₁.Perm s₂) (hu : KeysUnique s₁) : ctx.toNearState cfg s₁ = ctx.toNearState cfg s₂ := by
  unfold VMContext.toNearState
  rw [sortedKeys_perm h, lookup_perm h hu]

/-- Two outcomes that differ at most in the storage a failure echoes back. -/
def EchoRel (o₁ o₂ : VMOutcome) : Prop :=
  { o₁ with storage := [] } = { o₂ with storage := [] } ∧ (o₁.aborted = none → o₁.storage = o₂.storage)

theorem outcomeOfExecution_echo (ctx : VMContext) (s₁ s₂ : List (Bytes × Bytes)) (final : Machine)
    (err : Option FunctionCallError) :
    EchoRel (outcomeOfExecution ctx s₁ final err) (outcomeOfExecution ctx s₂ final err) := by
  unfold outcomeOfExecution
  dsimp only
  split
  · exact ⟨rfl, fun h => by cases h⟩
  · split
    · exact ⟨rfl, fun h => by simp [VMOutcome.graphIssue] at h⟩
    · split
      · exact ⟨rfl, fun h => by simp [VMOutcome.graphIssue] at h⟩
      · exact ⟨rfl, fun _ => rfl⟩

theorem failedBefore_echo (ctx : VMContext) (s₁ s₂ : List (Bytes × Bytes)) (burnt : Nat)
    (e : FunctionCallError) (profile : GasProfile) :
    EchoRel (VMOutcome.failedBefore ctx s₁ burnt e profile) (VMOutcome.failedBefore ctx s₂ burnt e profile) :=
  ⟨rfl, fun h => by cases h⟩

/-- Listing the storage differently changes only what a failure echoes back. -/
theorem runAttempt_perm (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) {s₁ s₂ : List (Bytes × Bytes)} (h : s₁.Perm s₂) (hu : KeysUnique s₁)
    (fuel : Nat) :
    EchoRel (runAttempt cfg code codeSize method ctx s₁ fuel)
      (runAttempt cfg code codeSize method ctx s₂ fuel) := by
  unfold runAttempt
  rw [toNearState_perm cfg ctx h hu]
  dsimp only
  repeat' (first | exact failedBefore_echo _ _ _ _ _ _ | exact outcomeOfExecution_echo _ _ _ _ _ | split)

theorem checkReceipts_echo {o₁ o₂ : VMOutcome} (balance usage : Nat) (s₁ s₂ : List (Bytes × Bytes))
    (h : EchoRel o₁ o₂) : EchoRel (o₁.checkReceipts balance usage s₁) (o₂.checkReceipts balance usage s₂) := by
  have hv : o₁.receiptsValid = o₂.receiptsValid := by
    have := congrArg VMOutcome.receiptsValid h.1
    simpa [VMOutcome.receiptsValid] using this
  unfold VMOutcome.checkReceipts
  rw [hv]
  split
  · exact h
  · refine ⟨?_, fun h => by simp [VMOutcome.graphIssue] at h⟩
    have := congrArg (fun o : VMOutcome => { VMOutcome.graphIssue balance usage [] o with storage := [] }) h.1
    simpa [VMOutcome.graphIssue] using this

theorem run_perm (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) {s₁ s₂ : List (Bytes × Bytes)} (h : s₁.Perm s₂) (hu : KeysUnique s₁)
    (fuel : Nat) :
    EchoRel (run cfg code codeSize method ctx s₁ fuel) (run cfg code codeSize method ctx s₂ fuel) :=
  checkReceipts_echo _ _ _ _ (runAttempt_perm cfg code codeSize method ctx h hu fuel)

end Wasm.Near
