import Wasm.MemoryLemmas

/-!
Linear-memory lemmas live in the dependency-free Wasm package so metered
runtime proofs and the separation logic share the same byte semantics.
This compatibility import preserves the existing `Wasm.Memory` API.
-/
