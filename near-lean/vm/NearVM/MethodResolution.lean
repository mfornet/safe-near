import NearVM.Run

/-!
# Calls to methods a module does not export

`runAttempt` looks the method up before any contract code runs: after the
loading charge and validation, a module without a start function and without
the method fails with `MethodNotFound` (or an earlier loading, validation or
empty-name failure). None of these is an execution issue.
-/

namespace Wasm.Near

theorem deduct_error {g : GasCounter} {burn use : Nat} {e : HostError}
    (h : (g.deduct burn use).2 = some e) : e = .gasExceeded ∨ e = .gasLimitExceeded := by
  unfold GasCounter.deduct at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    split <;> simp

theorem applyCharge_error {ns : NearState} {c : Charge} {e : HostError}
    (h : (applyCharge ns c).2 = some e) : e = .gasExceeded ∨ e = .gasLimitExceeded := by
  cases c <;> simp only [applyCharge] at h <;>
    exact deduct_error (by simpa [GasCounter.burn, GasCounter.payAction, GasCounter.prepay] using h)

/-- Charging only fails for gas. -/
theorem applyCharges_error {ns : NearState} {cs : List Charge} {e : HostError}
    (h : (applyCharges ns cs).2 = some e) : e = .gasExceeded ∨ e = .gasLimitExceeded := by
  induction cs generalizing ns with
  | nil => cases h
  | cons c cs ih =>
    simp only [applyCharges] at h
    cases hc : applyCharge ns c with
    | mk ns' err =>
      rw [hc] at h
      cases err with
      | none => exact ih h
      | some e' =>
        simp only [Option.some.injEq] at h
        subst h
        exact applyCharge_error (by rw [hc])

@[simp] theorem prepareMemory_start (cfg : RuntimeConfig) (code : Module) :
    (prepareMemory cfg code).start = code.start := rfl

@[simp] theorem prepareMemory_exportFunc (cfg : RuntimeConfig) (code : Module) (name : String) :
    (prepareMemory cfg code).exportFunc? name = code.exportFunc? name := rfl

/-- A method a module without a start function does not export fails before
execution, with an error that is no execution issue. -/
theorem runAttempt_not_exported (cfg : RuntimeConfig) (code : Module) (codeSize : Nat)
    (method : String) (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Nat)
    (hstart : code.start = none) (hexport : code.exportFunc? method = none) :
    ∃ burnt e profile, runAttempt cfg code codeSize method ctx storage fuel =
      VMOutcome.failedBefore ctx storage burnt e profile ∧ e.issue? = none := by
  unfold runAttempt
  dsimp only
  split
  · exact ⟨_, _, _, rfl, rfl⟩
  split
  · exact ⟨_, _, _, rfl, rfl⟩
  · cases hload : applyCharges (ctx.toNearState cfg storage) (loadingCharges codeSize) with
    | mk host1 loadErr =>
      dsimp only
      cases loadErr with
      | some e =>
        refine ⟨_, _, _, rfl, ?_⟩
        rcases applyCharges_error (by rw [hload]) with rfl | rfl <;> rfl
      | none =>
        dsimp only
        split
        · exact ⟨_, _, _, rfl, rfl⟩
        · simp only [prepareMemory_start, hstart, Option.isSome_none, Bool.false_eq_true, ite_false,
            prepareMemory_exportFunc, hexport]
          split
          · exact ⟨_, _, _, rfl, rfl⟩
          · exact ⟨_, _, _, rfl, rfl⟩

/-- The same at the public VM boundary. -/
theorem run_not_exported (cfg : RuntimeConfig) (code : Module) (codeSize : Nat)
    (method : String) (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) (fuel : Nat)
    (hstart : code.start = none) (hexport : code.exportFunc? method = none) :
    ∃ burnt e profile, run cfg code codeSize method ctx storage fuel =
      VMOutcome.failedBefore ctx storage burnt e profile ∧ e.issue? = none := by
  obtain ⟨burnt, e, profile, h, hi⟩ := runAttempt_not_exported cfg code codeSize method ctx storage fuel hstart hexport
  refine ⟨burnt, e, profile, ?_, hi⟩
  unfold run
  rw [h]
  rfl

end Wasm.Near
