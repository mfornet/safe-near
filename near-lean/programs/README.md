# Programs

Small Rust programs compiled to Wasm and run under the `near-lean` WASM
interpreter (`../wasm`). They are test inputs for the runtime: each is a
zero-argument export that reads bytes from the `stdio` host, computes, and
writes bytes back.

Copied from [Talos](https://github.com/cajal-technologies/talos) `programs/`
at commit `80644390de3ad4db3055445259a034413ae41577` (2026-10-06), with the
specifications. `ByteEcho` now has a kernel-checked correctness proof of its
compiled export. The GCD kernel and exported stream driver are proved
through Iris and small-step termination. The mergesort export has an
outcome-sensitive partial-correctness proof. All four specifications are proved.
The port includes proof support for these theorems. The package depends on `../iris-wasm` (Talos's `codelib`), exactly as upstream does.
License AGPL-3.0, see `../wasm/LICENSE`.

| Program | Export | Stream contract |
|---|---|---|
| `byte_echo` | `byte_echo` | Reads one byte and writes it back. Empty input, empty output. |
| `gcd_stdio` | `gcd` | Reads two little-endian `u64`, writes their GCD (via the `num-integer` crate) as one. Short input, no output. |
| `mergesort` | `mergesort` | Reads little-endian `u32`s, writes them sorted. Input not a multiple of 4 bytes, no output. |

Support crates: `talos_stdio` (bump allocator over `talos.oom`, plus
`stdio.read`/`stdio.write` imports with `(length, pointer)` argument order) and
`gcd_talos_stdio` (a fixed-size variant used only by `gcd_stdio`).

## Layout

```
rust/                     cargo workspace, toolchain pinned in rust-toolchain.toml
  build.sh                cargo → wasm-tools strip/print → build/<crate>/program.{wasm,wat}
  build/<crate>/          committed build outputs (what the Lean side consumes)
lean/                     Lake package `Programs`, depends on ../../iris-wasm (and so on ../../wasm)
  Programs/<Crate>/Program.lean   generated Wasm AST of each program (spliced from the .wat by CodeLib.Generated)
  Programs/<Crate>/Spec.lean      the specification (semantic Input/Output, host contract)
  Programs/<Crate>/Proof.lean     completed correctness theorem
  Programs/GcdStdio/KernelProof.lean  compiled Stein kernel partial correctness and termination
  Programs/Smoke.lean     `lake exe smoke`: runs every program on small inputs
```

## Specifications and proofs

Specs are `def … : Prop` tagged `@[spec_of <kind> "crate::fn"]`; the theorem
that discharges one is tagged `@[proves <spec>]` (attributes from
`CodeLib.Attrs`). All four statements below have completed proofs. The GCD and
mergesort proofs use the ported `CodeLib.SepLogic` framework.

| Spec | Kind | Statement | Theorem / status |
|---|---|---|---|
| `ByteEcho.Spec.ByteEchoSpec` | total | For every input byte, `byte_echo` terminates and writes exactly that byte. | `ByteEcho.Proof.byte_echo_correct` (proved) |
| `GcdStdio.Spec.KernelSpecification` | total, internal | The out-of-line `gcd_u64` kernel (`func1`), run on two `i64`s, returns `Nat.gcd`. | `GcdStdio.Proof.kernel_correct` (proved) |
| `GcdStdio.Spec.PublicEntrySpecification` | total | For every pair of `u64`, `gcd` terminates and writes their `Nat.gcd`. | `GcdStdio.Proof.gcd_correct` (proved) |
| `Mergesort.Spec.PublicEntrySpecification` | partial | Every finite run of `mergesort` on packed `u32`s either traps with the allocator's `talos.oom` or returns a sorted permutation of the input. Termination is not claimed. | `Mergesort.Proof.mergesort_correct` (proved) |

`ByteEcho.Proof.byte_echo_correct` symbolically evaluates the actual generated
module for an arbitrary input byte, including its allocator and universal-host
calls. Its 85-step witness is transported through `runSteps_result_terminates`
to the existing fuel-free total-correctness specification. It neither enumerates
sample inputs nor assumes a VM execution equation. No generated program or
specification was changed.

`Programs.ProofSupport.Cbv.program_cbv` fixes the pinned Lean 4.34.1 evaluator's
literal-conditional proof construction, supplying its missing `Decidable`
argument. The change is scoped to each tactic invocation. Kernel checking and
the axiom audit remain in force. The program audit uses the same strict
standard-axiom policy as the core libraries, with no `sorryAx` exception.

`GcdStdio/KernelProof.lean` adapts the [pinned Talos optimized Stein proof](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean)
to the existing generated `GcdStdio.func1` and `Spec.kernelConfig`. The Iris
partial-correctness invariant tracks the GCD of the positive odd parts and
recombines their common power of two. A separate finite-trace proof decreases
the sum of the two odd operands. Combining them proves the existing total
kernel specification, including both zero-input exits. No standalone Talos
program, alternate store or assumed execution equation is needed. The exported
stream theorem is completed by `Contracts`, `CallKernelProof`, `HostProof`,
`DriverProof` and `Adequacy`. The call proof frames arbitrary caller resources;
the host proofs establish concrete reads/writes from exclusive byte ownership.
The allocator prefix starts from the actual generated module's memory/globals
and supplies the sixteen-byte input buffer. Total outcome adequacy yields the
finite execution required by the unchanged public specification. Shared
`ProofSupport.StreamMemory`/`StreamHost` modules contain only byte ownership,
call framing and stdio transfers; no unrelated mergesort proof is imported.

The mergesort proof ports the [pinned Talos reachable-function proof chain](https://github.com/cajal-technologies/talos/tree/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/Mergesort).
`Representations` ties byte/word ownership, allocator freshness, vector capacity
and codec invariants to the physical state. `SortProof`, the local-function
contracts and the driver proof compose the actual generated functions. The
outcome adapter accounts for the precise `talos.oom` trap and host marker.
Partial adequacy proves the unchanged public statement for every finite
terminal execution. This does not claim termination or exclude the specified
OOM outcome. Generated code and public specifications remain unchanged.

All program modules build with `--wfail` and pass the strict package-wide axiom
audit. GCD uses its own generated register-only body and store, without adding
the standalone `num_integer_opt3` program. Terminal outcome-WP rules live in
`CodeLib.SepLogic.SmallStepOutcomeLifting`; compile-time examples reuse them.

## Build the Wasm

```
cd near-lean/programs/rust
./build.sh            # needs rustup and wasm-tools
```

The script mirrors Talos's `verifier build` (reproducible path remaps, all
custom sections stripped), and the resulting `.wat` files are byte-identical to
the ones Talos's committed `Program.lean` files were generated from. The
`WAT SHA-256` comment at the top of each `Program.lean` is the hash of the
`.wat` it was generated from. Each `Program.lean` also re-decodes its `.wat`
at compile time and fails if the AST differs, so a changed build cannot go
unnoticed; regenerating `Program.lean` needs Talos's `verifier emit`.

## Run the programs

```
cd near-lean/programs/lean
lake build --wfail    # proved Programs library, warnings treated as errors
lake exe smoke        # six cases across the three programs, exit 1 on mismatch
lake exe program-tests # exhaustive small mergesort inputs and stream boundaries
```

`Programs.Harness.run` is the reusable driver: it instantiates a module under
`Universal.envFor` (every host the interpreter knows, resolved by import name),
feeds it an input byte list and returns the output byte list. Its error type
distinguishes missing exports, unsupported imports, initialization errors,
traps, fuel exhaustion, and interpreter errors. `Programs.Smoke.runBytes`
retains the original `Option` adapter.

`Programs.Regression` compares compiled mergesort against Lean's sorting on
all lists of length 0–4 over `[0, 1, UInt32.max]`, plus sorted, reversed, and
duplicate-heavy inputs around merge and 256-byte stream boundaries. It also
checks malformed byte lengths, GCD boundary values, byte echo, and explicit
harness failures. Both the six smoke cases and the regression suite run in CI.
These executable checks complement the compiled program correctness proofs.
The stream harness requires a `() -> ()` export; exports requiring parameters
or returning Wasm values are rejected before execution. The regression suite
currently contains 168 cases.

The interpreter's CLI `runner` cannot run these programs: it rejects any module
with imports.
