import Interpreter.Wasm

/-!
# CodeLib.Basic — public re-exports

This module forwards the Wasm proof surface (typed AST,
fuel-bounded interpreter, `wp` framework, `TerminatesWith` predicate).
Generated `Program.lean` files use `CodeLib.Generated` instead, keeping
executable program tests independent of this proof umbrella.

The WAT decoder is intentionally **not** re-exported; it exists only as
internal scaffolding for the verifier's `.wasm → WAT → Lean source` pipeline
(see `verifier/Verifier/Emit.lean`).

Bundled worked examples are also kept out of this downstream surface; import
`Interpreter.Wasm.Examples.Basic` explicitly when developing the interpreter's
example corpus.
-/
