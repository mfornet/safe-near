import NearRuntime.Boundary
import NearVM.MethodResolution

/-!
# Unexported methods at the boundary

A call to a method the binary does not export fails before any contract code
runs: no effects and no execution issue, for every context and storage.
-/

namespace Near.Boundary

open NearInterface Wasm.Near

theorem failureOf_not_issue {e : FunctionCallError} (h : e.issue? = none) (msg : String) :
    failureOf e ≠ .executionIssue msg := by
  unfold failureOf
  rw [h]
  dsimp only
  split <;> simp

theorem execOn_not_exported (code : Code) (storage : List (Bytes × Bytes)) (ctx : Context)
    (hissue : code.code.decodeIssue = none) (hstart : code.code.module.start = none)
    (hexport : code.code.module.exportFunc? ctx.method = none) :
    RolledBack ctx storage.toFinset (execOn code storage ctx) ∧
      ∀ msg, (execOn code storage ctx).outcome ≠ .error (.executionIssue msg) := by
  obtain ⟨burnt, e, profile, hrun, hi⟩ := run_not_exported ctx.protocol code.code.module code.code.size
    ctx.method (toVMContext ctx) storage (fuelFor ctx.protocol code.code.module (toVMContext ctx)) hstart hexport
  have hobs : execOn code storage ctx =
      observe ctx storage (VMOutcome.failedBefore (toVMContext ctx) storage burnt e profile) none := by
    unfold execOn
    simp only [hissue]
    rw [hrun]
    rfl
  have hout : (execOn code storage ctx).outcome = .error (failureOf e) := by
    rw [hobs]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hobs]
    exact observe_rolledBack _ _ _ _ (by rw [← hobs]; exact hout)
  · intro msg h
    rw [hout] at h
    exact failureOf_not_issue hi msg (Except.error.inj h)

/-- The same for near-lean's `RuntimeInterface`. -/
theorem nearRuntime_not_exported (code : Code) (raw : RawStorage) (ctx : Context)
    (hissue : code.code.decodeIssue = none) (hstart : code.code.module.start = none)
    (hexport : code.code.module.exportFunc? ctx.method = none) :
    RolledBack ctx raw (nearRuntime.exec code raw ctx) ∧
      ∀ msg, (nearRuntime.exec code raw ctx).outcome ≠ .error (.executionIssue msg) := by
  have h := execOn_not_exported code raw.toList ctx hissue hstart hexport
  rw [Finset.toList_toFinset] at h
  exact h

end Near.Boundary
