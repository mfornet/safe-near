# Wasm runtime

A WebAssembly runtime in Lean 4, written from the
[core specification](https://webassembly.github.io/spec/core/) and driven by
the official spec testsuite. It replaced the AGPL-licensed Talos interpreter;
the design is in [notes/design/WASM_RUNTIME.md](../../notes/design/WASM_RUNTIME.md)
and the rewrite plan, kept for the record, in
[notes/history/wasm_runtime_rewrite.md](../../notes/history/wasm_runtime_rewrite.md).

## Clean-room rule

Nothing in this package may be copied, translated or paraphrased from Talos
(https://github.com/cajal-technologies/talos). Write from the specification
and the testsuite; reviewers check against the specification, not against
Talos.

Reviewing a change to this package means two things: the behaviour is the
specification's (cite the section), and the text is not Talos's. The second
check compares the change against the Talos copy kept in git history at
commit `99435f7` (`git show 99435f7:near-lean/wasm/Interpreter/...`) for shared
comments, identifiers beyond what the spec dictates, layouts and proof scripts.
[REVIEW.md](REVIEW.md) records that review for the initial runtime.

## Scope

The features nearcore enables: the MVP, mutable globals, sign extension,
saturating float-to-int, floats with canonical NaNs, reference types and bulk
memory. SIMD, threads, tail calls, multi-memory, memory64, exceptions, GC and
function references are rejected as `unsupported`, distinct from `malformed`.

## Layout

| Module | Spec section | Status |
|---|---|---|
| `Wasm/Syntax.lean` | 2 Structure | the AST, NEAR feature set plus multi-value |
| `Wasm/Binary.lean` | 5 Binary format | decoder; `malformed` and `unsupported` are distinct errors; reads its input through a function (`Input.read`) |
| `Wasm/ByteSource.lean`, `Wasm/BinaryReads.lean` | | bytes the kernel reads in a few steps, so proofs can run the decoder on a large binary; lemmas that put decoded pieces together (`Reads`, `count_of_reads`, `body_eq`) |
| `Wasm/Validate.lean` | 3 Validation | type checker with `Features`; `Features.nearcore` is what nearcore accepts |
| `Wasm/Value.lean`, `Wasm/Numeric.lean` | 4.3 Numerics | values as bit patterns; integer ops on `UInt32`/`UInt64`, float ops through `Float32`/`Float` with canonical NaNs |
| `Wasm/Memory.lean`, `Wasm/Store.lean` | 4.2 Runtime structure | paged memory, the store, host functions and host modules |
| `Wasm/Exec.lean` | 4.4 Instructions | one executable `step`; `Step` and `Steps` are defined from it |
| `Wasm/HostInvariant.lean` | | a step preserves any host-state predicate the host functions preserve |
| `Wasm/Link.lean` | 4.5 Modules | instantiation, import checking, name registry |
| `Wasm/LinkInvariant.lean` | | instantiation keeps the host state and adds no host function |
| `Wasm/Bytes.lean`, `Wasm/Wat.lean` | | byte-array and UTF-8 facts; `wasm-tools`-backed WAT compilation for tests |
| `Wasm/Host/Spectest.lean` | | the testsuite's `spectest` module |
| `WasmEmbed/` | | out of `Wasm`'s import closure: `byte_source%`, `#embed_wasm_code`, `#embed_wasm_sections` and `kernel_rfl`, which embed a binary and state what it decodes to, for the kernel to check |
| `Testsuite/` | | runs every command kind; `testsuite_out_of_scope.txt` lists whole files outside scope |
| `Cli/` | | `lake exe wasm decode FILE.wasm`, `lake exe wasm validate FILE.wasm` |

Spec testsuite at the pinned revision: 33595 commands pass, 0 fail; the rest
are out of scope (SIMD, GC, memory64, multi-memory, exceptions, tail calls,
function references, extended const, text-form assertions) or refer to an
out-of-scope module. The whole suite runs in about 8 s.

## Build and test

```
lake build                    # the library, no dependencies beyond core Lean
lake build testsuite wasm     # the executables
scripts/testsuite.sh          # whole suite; scripts/testsuite.sh i32 for a subset
scripts/testsuite-report.sh   # regenerate testsuite_report.txt (pinned wasm-tools)
scripts/testsuite-summary.sh  # totals per outcome from the committed report
```

The testsuite needs `wasm-tools` 1.251.0 (`cargo install wasm-tools@1.251.0`)
to split `.wast` scripts, and the submodule `vendor/testsuite` pinned to the
same revision as before (initialised by the scripts). `WASM_TESTSUITE` or
`--dir` points elsewhere.

`testsuite_report.txt` has one line per testsuite command with its outcome:

- `pass`: as the spec says.
- `fail`, `decode_error`: bugs. The driver exits 1.
- `out_of_scope:<feature>`: the module uses a feature we do not support.
- `skipped:<kind>`: the driver does not run that command kind yet.
- `module_unavailable`: the command refers to a module that did not load.

CI regenerates the report and fails if it differs from the committed one, so
a change in coverage is committed with the code that caused it.
