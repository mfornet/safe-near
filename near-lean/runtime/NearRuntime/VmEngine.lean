import NearVM.Run

/-!
# The VM engine a chunk is applied with

`Wasm.Near.run` is the specification of a contract call, and what contract verification reasons about. A node
that applies chunks as they arrive needs a faster `Impl` of the same function (`NearFastVM.run`), which it
cannot prove equal to the specification yet; differential tests compare the two. `VmEngine` is how the
runtime is given one: every definition between `Near.apply` and the function-call action takes it as an
instance argument, and the default instance is the specification, so every statement about these definitions
(and every proof) is about `Wasm.Near.run` unless a caller names another engine.
-/

namespace Near

open Wasm Wasm.Near

class VmEngine where
  /-- `Wasm.Near.run`'s signature without its fuel argument. -/
  run :
    RuntimeConfig → Module → Nat → String → VMContext → List (List UInt8 × List UInt8) → VMOutcome

/-- The specification. -/
instance (priority := low) VmEngine.spec : VmEngine :=
  ⟨fun cfg code codeSize method ctx storage => Wasm.Near.run cfg code codeSize method ctx storage⟩

/-- With the default instance the engine is `Wasm.Near.run`; the proofs about the runtime rewrite with it. -/
@[simp]
theorem VmEngine.spec_run (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) :
    @VmEngine.run VmEngine.spec cfg code codeSize method ctx storage =
      Wasm.Near.run cfg code codeSize method ctx storage :=
  rfl

end Near
