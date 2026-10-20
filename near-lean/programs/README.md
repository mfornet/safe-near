# Programs

Small Rust programs compiled to Wasm and run under the `near-lean` WASM
interpreter (`../wasm`). They are test inputs for the runtime: each is a
zero-argument export that reads bytes from the `stdio` host, computes, and
writes bytes back.

Copied from [Talos](https://github.com/cajal-technologies/talos) `programs/`
at commit `80644390de3ad4db3055445259a034413ae41577` (2026-10-06), with the
specifications. `ByteEcho` now has a kernel-checked correctness proof of its
compiled export, and the compiled GCD kernel is proved through Iris and
small-step termination. The GCD stream and mergesort theorems remain open in
`Proof.lean` files. The port includes proof support for the completed theorems.
The package
depends on `../iris-wasm` (Talos's `codelib`), exactly as upstream does.
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
  Programs/<Crate>/Proof.lean     the correctness theorem (GCD stream/mergesort remain open)
  Programs/GcdStdio/KernelProof.lean  compiled Stein kernel partial correctness and termination
  Programs/Smoke.lean     `lake exe smoke`: runs every program on small inputs
```

## Specifications and open proofs

Specs are `def … : Prop` tagged `@[spec_of <kind> "crate::fn"]`; the theorem
that discharges one is tagged `@[proves <spec>]` (attributes from
`CodeLib.Attrs`). Everything below is stated and typechecks. The ByteEcho and GCD kernel proofs are complete;
the other two proofs remain `sorry`. Upstream's proofs are separation-logic proofs over
`CodeLib.SepLogic`, which is now available here.

| Spec | Kind | Statement | Theorem / status |
|---|---|---|---|
| `ByteEcho.Spec.ByteEchoSpec` | total | For every input byte, `byte_echo` terminates and writes exactly that byte. | `ByteEcho.Proof.byte_echo_correct` (proved) |
| `GcdStdio.Spec.KernelSpecification` | total, internal | The out-of-line `gcd_u64` kernel (`func1`), run on two `i64`s, returns `Nat.gcd`. | `GcdStdio.Proof.kernel_correct` (proved) |
| `GcdStdio.Spec.PublicEntrySpecification` | total | For every pair of `u64`, `gcd` terminates and writes their `Nat.gcd`. | `GcdStdio.Proof.gcd_correct` |
| `Mergesort.Spec.PublicEntrySpecification` | partial | Every finite run of `mergesort` on packed `u32`s either traps with the allocator's `talos.oom` or returns a sorted permutation of the input. Termination is not claimed. | `Mergesort.Proof.mergesort_correct` |

`ByteEcho.Proof.byte_echo_correct` symbolically evaluates the actual generated
module for an arbitrary input byte, including its allocator and universal-host
calls. Its 85-step witness is transported through `runSteps_result_terminates`
to the existing fuel-free total-correctness specification. It neither enumerates
sample inputs nor assumes a VM execution equation. No generated program or
specification was changed.

`Programs.ProofSupport.Cbv.program_cbv` fixes the pinned Lean 4.34.1 evaluator's
literal-conditional proof construction, supplying its missing `Decidable`
argument. The change is scoped to each tactic invocation. Kernel checking and
the axiom audit remain in force. The program audit permits the two open
proofs but requires `Programs.ByteEcho.Proof` and `Programs.GcdStdio.KernelProof`
to remain completely free of nonstandard axioms, including `sorryAx`.

`GcdStdio/KernelProof.lean` adapts the [pinned Talos optimized Stein proof](https://github.com/cajal-technologies/talos/blob/80644390de3ad4db3055445259a034413ae41577/programs/lean/Project/NumIntegerOpt3/Spec.lean)
to the existing generated `GcdStdio.func1` and `Spec.kernelConfig`. The Iris
partial-correctness invariant tracks the GCD of the positive odd parts and
recombines their common power of two. A separate finite-trace proof decreases
the sum of the two odd operands. Combining them proves the existing total
kernel specification, including both zero-input exits. No standalone Talos
program, alternate store or assumed execution equation is needed. The exported
stream theorem still needs its allocator/codec/host-call bridge.

Upstream Talos proves all four. The GCD kernel spec there is tied to the
separately verified `num_integer_opt3` program, which is not in near-lean, so
`kernelConfig` here uses this module's own (irrelevant) store and the
body-equality theorem is omitted. `lake build` reports the open `sorry`s as
warnings.

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
lake build            # Programs library
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
These are executable checks; `Mergesort.Proof.mergesort_correct` remains open.
The stream harness requires a `() -> ()` export; exports requiring parameters
or returning Wasm values are rejected before execution. The regression suite
currently contains 168 cases.

The interpreter's CLI `runner` cannot run these programs: it rejects any module
with imports.
