# iris-wasm

The proof layer on top of the WASM interpreter (`../wasm`): an
[Iris](https://github.com/leanprover-community/iris-lean) separation logic for
Wasm, lifting lemmas from small-step traces to the logic, adequacy theorems
back to the executable semantics, Rust std lemmas, host contracts, and worked
examples.

This is a **copy** of the `codelib/` package of
[Talos](https://github.com/cajal-technologies/talos), not a submodule, taken at
the same commit as `../wasm`:

| Provenance | |
|---|---|
| Upstream | https://github.com/cajal-technologies/talos `codelib/` |
| Commit | `80644390de3ad4db3055445259a034413ae41577` (2026-10-06) |
| License | AGPL-3.0, see [../wasm/LICENSE](../wasm/LICENSE) |
| Iris | `leanprover-community/iris-lean` at `04b7689c294bb1dd6401e2dd53b337871934ea47` (git dependency, subdir `Iris`) |

The Lake package and module are still called `CodeLib` to keep diffs against
upstream small; only the interpreter dependency was repointed from
`../interpreter` to `../wasm`. Nothing was dropped.

## What is in it

- `CodeLib/SepLogic/`: `WasmHeap` (points-to for linear memory, locals,
  globals, host state), `WasmRules` (Hoare rules per instruction),
  `SmallStepLifting` / `SmallStepTotalLifting` (from the executable small-step
  semantics into the logic), `SmallStepAdequacy` / `SmallStepOutcomeAdequacy`
  (from a logic proof back to a statement about real runs, including the
  distinguished OOM trap), plus worked examples (host calls, two modules,
  shared memory, import chains, exception lifecycle).
- `CodeLib/RustStd/`: lemmas about code rustc emits for std operations
  (`u64` arithmetic, arrays, `Vec`, memory copy and fill loops, frames,
  regions, borsh).
- `CodeLib/Host/`: StdIO and universal-host contracts in the logic.
- `CodeLib/Examples/`: Gcd, MergeSort, Quicksort, SelectionSort with full
  proofs, both pure and as StdIO stream programs.
- `CodeLib/Near/`: an early NEAR host model (state, env, small step, a
  key-value setter example). A starting point for `../runtime`, not the
  design.
- `CodeLib/Generated.lean`: the `watFunctionBody%` / `watModuleMetadata%`
  elaborators and `checkWatFidelity` used by every generated `Program.lean`.
  It imports AST tooling and link attributes directly, so executing generated
  programs does not pull in Iris or the CodeLib proof examples. The program
  regression harness's local import closure contains 25 modules rather than
  119; only `CodeLib.Generated` and `CodeLib.Attrs` are from CodeLib.
- `CodeLib/Attrs.lean`: `@[spec_of]` and `@[proves]`.
- `CodeLib/IEEE32/Exec.lean`: declares the float bridge axioms; a build root
  but deliberately not reachable from the `CodeLib` umbrella.

## Build

```
cd near-lean/iris-wasm
lake build            # first run clones and compiles Iris, no binary cache exists for it
```

CI builds this package with `--wfail` and runs the axiom audit
(`tools/axiom-audit.py`, see [../README.md](../README.md)).
