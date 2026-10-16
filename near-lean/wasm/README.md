# WASM interpreter

A WebAssembly interpreter written in Lean 4. The same definitions that execute a
Wasm program are the ones proofs reason about.

This is a **copy** of the `interpreter/` package of
[Talos](https://github.com/cajal-technologies/talos), not a submodule: it is the
WASM runtime of `near-lean`, so it lives here where it can be audited and
modified alongside the NEAR runtime that plugs into it.

| Provenance | |
|---|---|
| Upstream | https://github.com/cajal-technologies/talos |
| Commit | `80644390de3ad4db3055445259a034413ae41577` (2026-10-06, "interpreter: reject reads of uninitialized non-defaultable locals (#250)") |
| License | AGPL-3.0, see [LICENSE](LICENSE) (kept verbatim from upstream) |
| Spec testsuite | `vendor/testsuite` submodule pinned to `9233a0a8d5920a8d32358ee915a3662ff3385029`, the same revision Talos pins |

## What was copied and what was left out

Copied, with paths flattened so that this directory is the Lake package:

- `Interpreter/` and `Interpreter.lean`: Wasm AST, decoder, validator, semantics
  (small step + continuation), WP calculus, hosts, worked examples.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` (Lean `v4.34.1`,
  Mathlib `v4.34.1`).
- `samples/`: tiny `.wat` modules used by the smoke test.
- `scripts/`: testsuite and smoke-test drivers from the Talos root, with paths
  adapted to this layout.
- `testsuite_report.txt`: the committed spec-testsuite coverage snapshot.

Left out on purpose (they are not part of the runtime; bring them in later if
needed): `codelib/` (Iris separation logic layer, Rust std lemmas, a NEAR host
experiment), `programs/` (Rust-to-Wasm proof projects), `verifier/`
(scaffolder / WAT emitter), `differential/` (fuzzing against V8), and the
agent configuration files.

The Lake module is still called `Interpreter` to keep diffs against upstream
small.

## Requirements

- [elan](https://github.com/leanprover/elan). The toolchain in `lean-toolchain`
  is fetched automatically.
- [wasm-tools](https://github.com/bytecodealliance/wasm-tools): decodes `.wasm`
  binaries and splits `.wast` scripts for the testsuite. The committed report is
  pinned to version `1.251.0` (see `scripts/testsuite-report.sh`):
  `cargo install wasm-tools@1.251.0`.
- [just](https://github.com/casey/just) is optional; every recipe in the
  `justfile` is a one-line `lake` or `scripts/` call you can run by hand.

Lake packages are shared with the sibling packages of `near-lean/` through
`packagesDir = "../.lake/packages"`.

## Build and run

```
cd near-lean/wasm
lake exe cache get                          # Mathlib prebuilt oleans
lake build Interpreter runner testsuite     # or: just build

lake exe runner samples/factorial.wat fact 5    # prints 120
lake exe runner --fuel 10000 samples/sum_to.wat sum_to 10
scripts/runner-smoke.sh                     # or: just runner-smoke
```

## Spec testsuite: where we are

The official [WebAssembly spec testsuite](https://github.com/WebAssembly/testsuite)
is the primary coverage signal. The submodule is initialised on first use.

```
scripts/testsuite.sh            # whole suite, human-readable per-file report
scripts/testsuite.sh i32        # only .wast files whose name contains "i32"
scripts/testsuite-summary.sh    # aggregate the committed report
scripts/testsuite-report.sh     # regenerate testsuite_report.txt (pinned wasm-tools)
```

`testsuite_report.txt` has one sorted line per testsuite command with its
outcome. CI regenerates it and fails if it drifts, so a change that shifts
coverage must commit the updated report in the same commit. Outcome meanings:

- `pass`: behaved as the spec says.
- `skipped:*`, `decode_error`, `module_unavailable`: feature not implemented.
  Not a failure.
- `fail`, `interpreter_error`, `out_of_fuel`: real bugs. The testsuite exits
  non-zero on these.

Snapshot at the upstream commit above (run `scripts/testsuite-summary.sh` for
the live per-file breakdown):

| | |
|---|---|
| Commands passing | 64769 / 65142 |
| Files fully passing | 215 / 257 |
| Real failures | 0 |

The remaining 373 commands are unimplemented features, grouped by outcome:

| Outcome | Count | What is missing |
|---|---|---|
| `skipped:assert_unlinkable` | 200 | Link-time checks when instantiating against imports (`imports*.wast`, `linking*.wast`, `memory64-imports.wast`) |
| `skipped:assert_invalid:` | 58 | Validator does not yet reject some invalid modules (GC arrays/structs, `br_on_cast`, memory, ref types) |
| `skipped:non-integer-expected` | 52 | Assertions whose expected result is a reference value (`ref_null.wast`, `br_table.wast`, ...) |
| `decode_error` | 27 | Decoder gaps: annotations, some `elem` segment forms |
| `module_unavailable` | 18 | Follow-on commands of a module that failed to decode |
| `skipped:assert_exhaustion` | 15 | Call-stack exhaustion is not modelled |
| `skipped:assert_malformed:` | 3 | A few malformed binaries are accepted |

## Syncing with upstream

Talos moves quickly. To pull in newer changes, diff this directory against
`interpreter/` of the upstream repository at the commit recorded above, apply
what is wanted, update the commit in this README, and regenerate
`testsuite_report.txt`.

## Programs

Rust stream programs compiled to Wasm and run under this interpreter live in
[`../programs`](../programs/README.md).
