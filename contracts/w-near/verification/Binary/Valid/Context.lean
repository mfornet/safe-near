import Binary.Module
import Wasm.Validate

/-!
# `contract.wasm` validates: the context

nearcore validates the module after replacing its memory declaration with
the protocol's limits (v86: 1024 pages initially, at most 2048).
`validate_wPrepared` proves that module valid. As for decoding, the kernel
checks it in pieces: everything but the bodies (`context_wPrepared`), then
the bodies of each of the 22 ranges of `Binary.Code` in its own theorem.
-/

namespace WNear.Binary

open Wasm

/-- The module with the memory nearcore declares under v86's limits. -/
noncomputable def wPrepared : Module :=
  { wNearModule with mems := wNearModule.mems.map fun _ =>
      { type := { limits := { min := 1024, max := some 2048 } } } }

/-- The context the bodies are checked in. -/
noncomputable def wCtx : Validate.Context :=
  match Validate.moduleContext (Features.nearcore true) wPrepared with
  | .ok c => c
  | .error _ => { features := Features.nearcore true, types := #[], funcs := #[], tables := #[], mems := #[], globals := #[], elems := #[], datas := 0, locals := #[], refs := #[], «return» := none }

theorem context_wPrepared : Validate.moduleContext (Features.nearcore true) wPrepared = .ok wCtx := by
  kernel_rfl

/-- Every function of a range validates. -/
def RangeOk (fs : List Func) : Prop := (fs.all fun f => (Validate.funcOk wCtx f).toBool) = true

theorem rangeOk_append {a b : List Func} (ha : RangeOk a) (hb : RangeOk b) : RangeOk (a ++ b) := by
  unfold RangeOk at *
  rw [List.all_append, ha, hb]; rfl

theorem rangeOk_mem {fs : List Func} (h : RangeOk fs) {f : Func} (hf : f ∈ fs) :
    Validate.funcOk wCtx f = .ok () := by
  have := List.all_eq_true.mp h f hf
  cases hv : Validate.funcOk wCtx f with
  | ok u => rfl
  | error e => rw [hv] at this; cases this

end WNear.Binary
