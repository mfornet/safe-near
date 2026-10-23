# WasmLogic

A separation logic over the Wasm runtime in [`../wasm`](../wasm/README.md),
built on [iris-lean](https://github.com/leanprover-community/iris-lean)
(pinned by revision in `lakefile.toml`). Phase 4 of
[notes/todo/wasm_runtime_rewrite.md](../../notes/todo/wasm_runtime_rewrite.md).
The clean-room rule of [`../wasm/README.md`](../wasm/README.md) applies to this
package too: it is written from iris-lean and the runtime, never from the
removed Talos layer `iris-wasm`; the independent review is recorded in
[`../wasm/REVIEW.md`](../wasm/REVIEW.md).

| Module | What it is |
|---|---|
| `WasmLogic/Language.lean` | The machine as an iris-lean `Language`: an expression is a running thread (with its limits) or a finished outcome, the state is the store, the primitive step is `Wasm.Exec.step`. Deterministic, silent, no forks; traps are values. `run_steps` ties `Exec.run` to the language's thread-pool steps. |
| `WasmLogic/Rules.lean` | Weakest-precondition rules from store ownership (`ownP`): `wp_step`, `wp_done`, `wp_trap` for one step, `wp_run` for a whole finishing run. |
| `WasmLogic/Adequacy.lean` | A closed resource family and `adequacy`: a WP proved from `ownP σ` with a pure postcondition holds of every finished `Exec.run`. |
| `WasmLogic/Examples/Sum.lean` | A counting loop (`block`, `loop`, `br_if`, locals): its WP specification, proved by letting the kernel run the machine, and the adequacy statement about every run. |

The resource is the whole store, so these rules do symbolic execution with
full ownership. Points-to assertions that split memory, locals and globals
into separately owned pieces are the next step and are not here yet.

```
lake build            # compiles iris-lean from source on first use
```

Proofs count only with the standard axioms: `python3 tools/axiom-audit.py
near-lean/wasm-logic --report audit/wasm-logic.json`.
