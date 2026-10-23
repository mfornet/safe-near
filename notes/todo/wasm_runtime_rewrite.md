# Wasm runtime rewrite: replacing the Talos interpreter

Status: phases 1 to 3 done on 2026-10-23: the runtime lives in `near-lean/wasm`,
`NearVM` runs on it with its proofs intact, and the Talos packages are gone.
Phase 4 (the Iris layer) is in `near-lean/wasm-logic`: language instance,
step and run rules, adequacy and an example; points-to assertions remain.

## Why

`near-lean/wasm`, `near-lean/iris-wasm` and `near-lean/programs` are copies of
[Talos](https://github.com/cajal-technologies/talos) under AGPL-3.0. We want a
Wasm runtime that is ours (permissive license, no upstream to track), much
smaller, fast enough to drive the conformance and scenario suites, and
compatible with the Wasm that nearcore accepts.

Where the Talos copy stands today, for reference:

| | Talos copy | Target |
|---|---|---|
| Lines of Lean (interpreter only) | ~35k, of which `SmallStep.lean` 7.7k, `Semantics.lean` 2.0k (a second semantics), `Decoder/Wat.lean` 3.4k | 5–7k |
| Features | MVP, GC, SIMD, exceptions, tail calls, memory64, multi-memory, function references | What nearcore enables (below) |
| Semantics | Executable function `stepChecked?` plus a separate 3.7k-line `Step` inductive, with determinism and agreement proofs between them | One executable `step`; the relation is defined from it |
| Module input | WAT only; `.wasm` goes through `wasm-tools print` first | Binary `.wasm` decoder in Lean |
| Linking | Single module plus positional host list; `linking.wast` and `imports*.wast` skipped (200 commands) | Spec store with multi-instance linking |
| Spec testsuite | 64769 / 65142 commands, 0 real failures, 373 skipped | 100% of the commands in scope, 0 skipped in scope |

## Compatibility target: what nearcore accepts

From nearcore `runtime/near-vm-runner/src/features.rs` at the pinned checkout
(`near-lean/runtime/reference.json`), the engine (wasmtime) is configured with:

| Feature | Enabled | Note |
|---|---|---|
| MVP (i32/i64/f32/f64, one memory, one table, globals, `call_indirect`) | yes | |
| `mutable_global` | yes | |
| `sign_extension` | yes | `i32.extend8_s` … `i64.extend32_s` |
| `saturating_float_to_int` | yes | `i32.trunc_sat_f32_s` … |
| `floats` | yes | NaN canonicalization on (`cranelift_nan_canonicalization(true)`): every float op producing NaN yields the canonical NaN |
| `reference_types`, `bulk_memory` | yes in the engine; gated per protocol version by `wasm_config.reftypes_bulk_memory` (false in every config we have up to v83) | phase 2 |
| `multi_value` | no | the runtime implements it (the spec suite uses it everywhere); the NEAR feature set disables it at validation |
| SIMD, threads, tail calls, multi-memory, memory64, exceptions, GC, function references, extended const, component model | no | never |

Beyond features, nearcore's `prepare` pass rejects modules against
`limit_config` (`max_functions_number_per_contract`, `max_locals_per_contract`,
`max_stack_height`, `max_tables_per_contract`, …) and instruments gas and stack
height (`finite-wasm`). Those stay in `NearVM`, where they live today
(`NearVM/Run.lean` meters per step from the outside). The runtime only needs
to expose what metering reads: the next instruction, the control stack, the
call depth, and a call-depth / stack-height limit that traps.

## Design

One Lake package, `near-lean/wasm`, Lake package `Wasm`, namespace `Wasm`.
Developed beside the Talos copy (as `near-lean/wasm-next`) until `NearVM` is
ported, then renamed into place and the copy deleted. No file of the new
package imports `Interpreter`, and no code is translated from Talos: it is
written from the [spec](https://webassembly.github.io/spec/core/) and the
testsuite. This is what makes the license change real.

```
near-lean/wasm/
  Wasm/Syntax.lean       AST: types, instructions, module (NEAR feature set only)
  Wasm/Binary.lean       .wasm decoder (LEB128, sections, code), malformed → DecodeError
  Wasm/Validate.lean     type checker (spec appendix algorithm) → ValidModule
  Wasm/Value.lean        values, integer ops, float ops (bit patterns + canonical NaN)
  Wasm/Memory.lean       linear memory with a small lemma API
  Wasm/Store.lean        store: function / table / memory / global instances, module instances
  Wasm/Host.lean         host functions, name-keyed host registries
  Wasm/Exec.lean         configuration, `step`, `run`, Steps, Terminates/Traps
  Wasm/Link.lean         instantiate: resolve imports from hosts and other instances, run start
  Wasm/Run.lean          the convenience API: decode → validate → instantiate → invoke
  Wasm/Host/Spectest.lean  the testsuite's `spectest` module
  Wasm/Host/StdIO.lean     byte-stream host, for non-NEAR example programs
  Testsuite/             driver for .wast via `wasm-tools json-from-wast` (kept)
  tests/                 unit tests for the decoder, validator and ops
```

### Semantics

A single, deterministic, executable small-step machine. The proof-side
relation is defined from it, so there is nothing to keep in sync:

```lean
structure Config (H : Type) where
  store  : Store H          -- functions, tables, memory, globals, host state
  thread : Thread           -- value stack, control labels, call frames

inductive StepResult (H : Type)
  | next (cfg : Config H)
  | done (values : List Value) (store : Store H)
  | trap (reason : Trap) (store : Store H)

def step : Config H → StepResult H            -- structural, kernel-reducible

def Step (c c' : Config H) : Prop := step c = .next c'
def Steps : Config H → Config H → Prop := Relation.ReflTransGen Step

def run (fuel : Nat) : Config H → RunResult H  -- iterate step; .outOfFuel is not a trap
```

`Config` is split as expression (`Thread`) and state (`Store`) from day one,
because that is the shape the Iris `Language` instance needs later.

Instructions are executed by structural recursion on the code list with an
explicit control stack (labels hold the continuation, as in the spec's reduction
with administrative instructions but without rebuilding the expression). The
value stack is a `List Value` or `Array Value`; profile before choosing.

### Values and floats

```lean
inductive Value | i32 : UInt32 → Value | i64 : UInt64 → Value
                | f32 : UInt32 → Value | f64 : UInt64 → Value   -- bit patterns
                | funcref : Option FuncAddr → Value | externref : Option Nat → Value  -- phase 2
```

Floats are stored as bit patterns and operated on through Lean's `Float32`
and `Float` (`ofBits` / `toBits`), followed by NaN canonicalization to match
nearcore. These operations are opaque to the kernel: proofs about float-using
code treat them as uninterpreted functions, and the spec testsuite (`f32.wast`,
`float_exprs.wast`, …) checks that execution is right. NEAR contracts we verify
do not compute with floats, so this costs nothing in practice. Integer
operations are plain `UInt32` / `UInt64` arithmetic, which the kernel reduces.

### Memory

`Memory` is an abstract type with a small lemma API (`read`, `write`,
`readBytes`, `writeBytes`, `grow`, `size`, and `get_set_same` / `get_set_ne`
style lemmas). Reference model `Array UInt8`; execution through
`@[implemented_by]` on `ByteArray` so updates are in place when the store is
used linearly. The `implemented_by` pair is the one place where "what runs" and
"what proofs see" differ; keep it to these few functions and test them against
each other. Decide after profiling whether `Array UInt8` alone is fast enough
(it is also updated in place when unshared); start without `implemented_by`.

### Hosts: generic over arbitrary environments

A host function sees the host state and the caller's memory, and nothing else:

```lean
structure HostFn (H : Type) where
  type : FuncType
  call : H → Memory → List Value → HostOutcome H
  -- HostOutcome: .return values h mem | .trap reason h mem

structure Host (H : Type) where
  resolve : (module name : String) → Option (HostFn H)   -- name-keyed, order-free
  init : H
```

Hosts compose (`Host.union`, lenses from a composite state to each component
state as the Talos registry does today), so a module may import from several.
Import resolution happens once at instantiation: every import becomes an
`ExternVal` in the spec's sense, `.func addr` where `addr` points either to a
Wasm function of another instance or to a host function. Calls then never look
at names. This is what gives `linking.wast` and `register` for free, and it is
also what a NEAR cross-contract-call test harness or a WASI-like host would
need.

For proofs, a host is described by a contract, not an implementation:

```lean
abbrev HostContract (H) := H → Memory → List Value → HostOutcome H → Prop
structure HostSpec (H) where resolve : (module name : String) → Option (HostContract H)
def Host.Satisfies (host : Host H) (spec : HostSpec H) : Prop := ...
```

Theorems are stated for any host satisfying a spec; executables pick a host.
This is the pattern `NearVM` already uses (`HostFn.Preserves`,
`RuntimePreservesInvariant`) and it carries over.

Metering stays outside the runtime: `NearVM` keeps its loop
`charge (nextInstruction cfg); step cfg; charge (frameDelta …)`. The runtime
exposes `Config.nextInstruction?`, `Config.callDepth`, `Config.controlTop?`,
and takes a `Limits` (max call depth, max value-stack height) that makes
`step` trap with `.stackOverflow`, which is what `assert_exhaustion` tests.

### Running programs

```lean
-- Everything a test or a harness needs, in four steps or one.
def Module.decode   : ByteArray → Except DecodeError Module
def Module.validate : Features → Module → Except ValidationError ValidModule
def instantiate     : Store H → ValidModule → (imports : List ExternVal) → Except LinkError (Store H × Instance)
def invoke (fuel)   : Store H → FuncAddr → List Value → RunResult H

def runExport (fuel) (host : Host H) (code : ByteArray) (name : String) (args : List Value)
  : Except RunError (List Value × Store H)
```

`lake exe wasm run file.wasm export args…` is the CLI over `runExport` with the
StdIO host, replacing `runner`. Modules written by hand for tests are `.wat`
files compiled to `.wasm` by `wasm-tools parse` in the build script and read
as bytes; there is no WAT parser in Lean. A small Lean notation for building
`Module` values directly (for proof examples) can come later if wanted.

### Statements

Three ways to say what a program does, from cheapest to strongest:

1. Concrete runs, checked by evaluation: `invoke … = .ok [.i32 120]`. Used by
   unit tests and smoke tests, provable by `decide` / `rfl` for small runs
   because `step` is structural and integer-only paths reduce in the kernel.
2. Behaviour over all inputs, as plain propositions on `Steps`:
   ```lean
   def Terminates (c : Config H) (post : List Value → Store H → Prop) : Prop :=
     ∃ c', Steps c c' ∧ ∃ vs st, step c' = .done vs st ∧ post vs st
   def TrapsWith (c : Config H) (r : Trap) : Prop := ...
   def Safe (c : Config H) : Prop := ∀ c', Steps c c' → step c' ≠ .trap ..   -- except as allowed
   ```
   plus `RunsWith host code export args post` that bundles decode, validate,
   instantiate and `Terminates`. Proved by stepping lemmas (`step` unfolded by
   a `wasm_step` simp set) and induction for loops. Enough for small kernels.
3. Refinement against a model: `NearVM.run` as a `RuntimeInterface` instance,
   as `contracts/w-near/verification/Spec/Refinement.lean` already does.
   Unchanged by this work.

Iris (separation logic over `Steps`, points-to for memory, per-instruction
rules) is level 2 made scalable. It is a separate package later
(`near-lean/wasm-logic`), built on `Step` as the `Language` primitive step;
nothing in the runtime depends on it.

## Testing

Test driven from the official testsuite, pinned as now
(`near-lean/wasm/vendor/testsuite`). The driver keeps the current pipeline
(`wasm-tools json-from-wast`, one JSON script and `.wasm` files per `.wast`),
the `testsuite_report.txt` format and the CI drift check, and gains:

- `assert_malformed` (binary form) against the decoder, `assert_invalid`
  against the validator, `assert_unlinkable` against `instantiate`,
  `assert_exhaustion` against the limits, `register` and multi-module linking
  against the store, all `spectest` imports.
- A scope list: core `.wast` files for the enabled features. Files for
  disabled proposals (SIMD, GC, memory64, exceptions, tail calls, multi-memory,
  function references, multi-value forms) are expected to fail in
  `assert_invalid`/decode and are reported as `out_of_scope`, never as pass.
  The gate is 0 non-pass outcomes in scope.

Order of work, each step driven by the testsuite files that cover it:

1. Decoder: `binary.wast`, `binary-leb128.wast`, `custom.wast`, every `module`
   command in the suite decodes.
2. Validator: `assert_invalid` across the suite; `type.wast`, `func.wast`,
   `unreached-invalid.wast`.
3. Integers and locals: `i32`, `i64`, `int_exprs`, `int_literals`,
   `local_get/set/tee`, `const`, `nop`.
4. Control: `block`, `loop`, `if`, `br`, `br_if`, `br_table`, `return`,
   `labels`, `stack`, `unwind`, `call`, `call_indirect`, `fac`, `forward`,
   `func_ptrs`, `left-to-right`.
5. Memory: `memory`, `address`, `align`, `load`, `store`, `endianness`,
   `memory_grow`, `memory_size`, `memory_trap`, `memory_redundancy`, `data`.
6. Globals, tables, elements, start, exports, imports, linking: `global`,
   `table`, `elem`, `start`, `exports`, `imports`, `linking`.
7. Floats and conversions: `f32*`, `f64*`, `float_*`, `conversions`,
   including NaN canonicalization checks against nearcore's test.
8. Sign extension and saturating truncation (already in 3 and 7).
9. Phase 2: bulk memory and reference types (`bulk`, `memory_copy`,
   `memory_fill`, `memory_init`, `data_drop`, `table_*`, `ref_*`, `select`
   with types), behind `Features`.

Beyond the spec suite:

- Unit tests for the decoder and validator on hand-written bytes, and for
  memory and integer ops against reference definitions.
- The existing nearcore conformance (`just near-conformance`, wNEAR fixtures,
  strict field equality including gas) and the scenario suites
  (`just near-test`) are the compatibility gate once `NearVM` is ported.
- Differential run against the Talos copy before it is deleted: same wNEAR
  fixtures through old and new `NearVM.run`, outputs byte-equal.
- Performance: record the wall time of the testsuite and of
  `just near-conformance` on the Talos copy before starting, and require the
  new runtime to be at least as fast; the aim is several times faster.

## Migration

Each phase ends green on everything that was green before it.

**Phase 0, preparation.** Record baselines (testsuite report, timings). Agree
this note. Add the clean-room rule to `near-lean/wasm-next/README.md` and ask
reviewers to check it.

**Phase 1, runtime.** `near-lean/wasm-next` through testing steps 1–8. Also
`ByteEncoding` helpers (little-endian words, `ByteArray` lemmas) that
`NearVM/MethodEncoding.lean` and `w-near/Model/Borsh.lean` import today, as
`Wasm.Bytes`. Deliverable: testsuite green in scope, CLI runner, StdIO host
with a couple of sample programs.

**Phase 2, NEAR port.** Switch `NearVM` to the new API:

- `Run.lean`: `initConfig` / `stepChecked?` / `RunnerResult` → `instantiate` /
  `step` / `RunResult`; trap mapping from the new `Trap` type; stack limit
  from `Limits`.
- `State.lean`, `Host.lean`, `Metered.lean`, `HostDispatch.lean`: `HostFn`
  shape changes from "whole store" to "host state and memory". Mechanical.
- `InterpreterInvariant.lean`, `LiveInvariant.lean`, `MeteredInvariant.lean`,
  `ExecutionFrames.lean`: the host-invariant preservation proof becomes one
  lemma, "a step either leaves the host state alone or applies one host
  function", proved once in `Wasm.Exec`.
- Tests and conformance drivers (`vm/tests`, `vm/Conformance`,
  `runtime/Tests`, `chain`, `w-near/RuntimeTests`): `Decoder.Wat.decode` on
  `.wat` text → `Module.decode` on `.wasm` bytes; commit `w_near.wasm` beside
  the current `w_near.wat` and the tiny inline modules as `.wat` files
  compiled by the build script.

Gate: `just near-test`, `just near-conformance`, `just build w-near`,
`just wnear-audit`, periodic checks, all unchanged in outcome.

**Phase 3, removal.** Rename `wasm-next` to `wasm`. Delete the Talos
`near-lean/wasm`, `near-lean/iris-wasm` and `near-lean/programs` (all AGPL)
and `near-lean/wasm/LICENSE`. Update `README.md`, `near-lean/README.md`,
`notes/design/WASM_RUNTIME.md`, `PROJECT_STRUCTURE.md`, `justfile`, the
`wasm` and `programs` CI workflows, `tools/check_vm_dependencies.py`. The
proved sample programs (gcd, mergesort, byte echo) go with the copy; they were
Talos's proofs of Talos's programs.

**Phase 4, later and separate.** `near-lean/wasm-logic`: Iris `Language`
instance over `Step`, `WasmHeap` points-to, instruction rules, adequacy back
to `Terminates`. Our own small Rust sample programs under the StdIO host as
its examples. Only needed when a contract proof needs symbolic execution of
Wasm code rather than refinement at the `NearVM.run` boundary.

## Outcome (2026-10-23)

- `near-lean/wasm`: 18 modules, about 3.7k lines, no dependency beyond core
  Lean. Spec testsuite: 33595 commands pass, 0 fail, the rest out of scope;
  the whole suite runs in about 8 s. Decoder and validator agree with
  `wasm-tools` on all eleven on-chain contracts.
- `NearVM` runs on it with every proof intact: the host-invariant files became
  instances of `Wasm.HostInvariant` and `Wasm.LinkInvariant`; `runAttempt_cases`
  replaced four duplicated case analyses. nearcore conformance: 400 of 400
  observations identical, gas included. VM, runtime and chain scenarios: 103,
  179 and 46 passing. Axiom audits: 0 violations in every package and in the
  wNEAR proofs.
- The Talos packages are deleted; `tools/axiom-audit.py`, which had been
  adapted from Talos, was rewritten. An independent clean-room review
  (`near-lean/wasm/REVIEW.md`) found the runtime modules clean and the test
  driver front end and scripts condensed from the old harness; those were
  re-authored afterwards. No WAT parser: tests compile WAT with the
  pinned `wasm-tools`. Memory is paged `ByteArray`s with no `implemented_by`.
- Speed: the VM, runtime and chain scenario suites take 0.45 s, 0.50 s and
  0.25 s of CPU on the new runtime against 0.65 s, 0.72 s and 0.40 s on the
  Talos build of the same commit, same fixtures.
- An independent clean-room review (`near-lean/wasm/REVIEW.md`) found the
  runtime free of Talos text and design, and flagged the shell scripts and the
  testsuite driver as derived; both were rewritten from scratch before the
  push, with the committed report unchanged.
- Model gaps kept explicit (`notes/design/WASM_RUNTIME.md`): start functions,
  exported imports, nearcore's stack limiter.

## Decisions to confirm

1. Feature scope as in the table: MVP + mutable globals + sign extension +
   saturating truncation + floats first; bulk memory + reference types second;
   nothing else, ever. Multi-value is implemented but off in the NEAR feature
   set, to match nearcore.
2. No WAT parser in Lean. `.wasm` is the only input; `wasm-tools` (already a
   pinned CI tool) turns hand-written `.wat` into bytes at build time.
3. Floats as bit patterns computed with Lean's `Float32`/`Float` and
   canonicalized NaNs; opaque to the kernel. The alternative, a pure IEEE-754
   implementation in Lean, is a project of its own and not needed for NEAR.
4. `Memory` behind a lemma API, possibly with `implemented_by` on `ByteArray`
   if profiling shows `Array UInt8` is not enough.
5. Metering and nearcore's `prepare` limits stay in `NearVM`; the runtime
   only exposes the hooks and a stack limit.
6. Delete `iris-wasm` and `programs` in phase 3 (license), rebuild the logic
   layer later on the new semantics rather than porting Talos's.

## Risks

- Kernel reducibility versus speed pull in opposite directions (well-founded
  recursion, `Array` versus `List`, `implemented_by`). Mitigation: decide per
  module by measuring, keep `step` structural, keep the executable path and
  the proof path the same function everywhere except `Memory`.
- NaN and float corner cases differ between wasmtime and Lean's `Float`
  (which calls the C library). Mitigation: the testsuite float files plus
  nearcore's canonicalization test; floats are not on any proof path.
- The `NearVM` port touches ~15 files and the invariant proofs; the new
  `HostFn` shape must give the NEAR host everything it uses today (memory,
  registers, its own state). Verified by reading `NearVM/Host.lean` before
  freezing `HostFn`.
- Contributors who know Talos may reproduce it from memory. Mitigation: the
  clean-room rule in the README and review from the spec, not from Talos.
