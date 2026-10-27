import Skeleton.Model
import NearRuntime.BoundaryResolution

/-!
# Complete invalid-method clause for the walking module

Only `save` parses. Every other name is rejected by the actual runtime's
method resolution, including its contract-loading gas behavior. This clause
needs no trie, resource, gas-sufficiency or well-formed-context hypotheses.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near NearInterface

theorem exportFunc_none_of_ne_save (method : String) (h : method ≠ "save") :
    module.exportFunc? method = none := by
  simp [Module.exportFunc?, module, Ne.symm h]

/-- The actual list-storage boundary rejects every unparsed method and
reports no interpreter limitation. -/
theorem execOn_invalid_method (ctx : Context) (raw : Storage) (h : ctx.method ≠ "save") :
    RolledBack ctx raw.toFinset (Near.Boundary.execOn code raw ctx) ∧
      ∀ msg, (Near.Boundary.execOn code raw ctx).outcome ≠ .error (.executionIssue msg) :=
  Near.Boundary.execOn_not_exported code raw ctx rfl no_start
    (exportFunc_none_of_ne_save ctx.method h)

/-- The same unparsed-input clause for the precise RuntimeInterface used by
`Refines`, whose raw storage is a finite set. -/
theorem nearRuntime_invalid_method (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : RawStorage)
    (h : ¬ ∃ call, (model gasBound).Parses ctx.method ctx.args call) :
    RolledBack ctx raw (Near.Boundary.nearRuntime.exec code raw ctx) ∧
      ∀ msg, (Near.Boundary.nearRuntime.exec code raw ctx).outcome ≠ .error (.executionIssue msg) := by
  have hn : ctx.method ≠ "save" := by
    intro he
    exact h ⟨(), he⟩
  exact Near.Boundary.nearRuntime_not_exported code raw ctx rfl no_start
    (exportFunc_none_of_ne_save ctx.method hn)

end WNear.Skeleton
