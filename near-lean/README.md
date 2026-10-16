# near-lean

NEAR in Lean 4. Three Lake packages sharing one package cache
(`near-lean/.lake/packages`), forming a dependency chain:

| Package | Path | Purpose |
|---|---|---|
| `Interpreter` | [`wasm/`](wasm/README.md) | WASM interpreter: AST, decoder, validator, executable small-step semantics, WP calculus, hosts. Copy of Talos `interpreter/`. |
| `CodeLib` | [`iris-wasm/`](iris-wasm/README.md) | Iris separation logic over the interpreter, lifting and adequacy, Rust std lemmas, worked examples. Copy of Talos `codelib/`. |
| `Programs` | [`programs/`](programs/README.md) | Rust stream programs compiled to Wasm, their specs, open correctness theorems, smoke runner. |

All three pin the same Lean toolchain (`lean-toolchain` in each). The planned
`runtime/` (NEAR runtime as a host) and `sdk/` packages are not here yet.

## Axiom audit: no `sorry`, no `native_decide`

A finished proof may depend only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`. `tools/axiom-audit.py` checks the
transitive axioms of every declaration in a package (private helpers and proof
fields included) and fails on anything else, in particular `sorryAx` and
`Lean.ofReduceBool` (what `native_decide` and `decide +native` rely on).

```
tools/axiom-audit.py near-lean/wasm --report audit/wasm.json
tools/axiom-audit.py near-lean/iris-wasm --report audit/iris-wasm.json
tools/axiom-audit.py near-lean/programs/lean --report audit/programs.json --allow-sorry
```

`wasm` and `iris-wasm` must be clean. `programs` holds specs whose proofs are
open by design, so there `--allow-sorry` tolerates `sorryAx` alone and prints
each sorried declaration; any other nonstandard axiom still fails. CI runs all
three on every change under `near-lean/`. Pass `--no-build` to audit already
built artefacts.
