import Skeleton.Model

/-!
# No interpreter limitation on matched model branches

The independent walking model has only protocol failures and success. Thus
model matching discharges the interpreter-limitation clause on every matched
branch, including all sufficient-gas empty-base cases.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near NearInterface

/-- Every failure emitted by the independent save model is a protocol failure. -/
theorem matches_modelStep_no_issue
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : RawStorage) (st : Option Storage) (observation : Observation)
    (h : Matches (model gasBound) ctx raw observation (modelStep ctx st ())) :
    ∀ msg, observation.outcome ≠ .error (.executionIssue msg) := by
  unfold modelStep at h
  simp only [Id.run, pure] at h
  repeat' split at h
  all_goals simp only [Matches, ContractModel.ModelFailure.toFailure, model] at h
  all_goals intro msg he
  all_goals rw [h.1] at he
  all_goals cases he

end WNear.Skeleton
