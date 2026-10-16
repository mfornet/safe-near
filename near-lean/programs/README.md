# Programs

Small Rust programs compiled to Wasm and run under the `near-lean` WASM
interpreter (`../wasm`). They are test inputs for the runtime: each is a
zero-argument export that reads bytes from the `stdio` host, computes, and
writes bytes back.

Copied from [Talos](https://github.com/cajal-technologies/talos) `programs/`
at commit `80644390de3ad4db3055445259a034413ae41577` (2026-10-06), **with the
specifications but without the proofs**: each program's `Spec.lean` is ported
and its top-level correctness theorem is stated in `Proof.lean` with a `sorry`
body. No `*Proof.lean` machinery, `Analysis/`, or Talos `codelib` dependency
was brought over. License AGPL-3.0, see `../wasm/LICENSE`.

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
lean/                     Lake package `Programs`, depends on ../../wasm
  Programs/Generated.lean elaborators that splice a .wat into Lean at compile time
  Programs/<Crate>/Program.lean   generated Wasm AST of each program
  Programs/<Crate>/Spec.lean      the specification (semantic Input/Output, host contract)
  Programs/<Crate>/Proof.lean     the correctness theorem, proof is `sorry`
  Programs/Attrs.lean     `@[spec_of]` / `@[proves]` attributes linking specs to code and proofs
  Programs/WordCodec.lean fixed-width packed byte codecs (`serialize`/`deserialize` round trip)
  Programs/WordCodec/UInt64.lean  the little-endian u64 codec
  Programs/ByteReassembly.lean    kernel-checked byte reconstruction lemmas behind the codecs
  Programs/Smoke.lean     `lake exe smoke`: runs every program on small inputs
```

## Specifications and open proofs

Specs are `def … : Prop` tagged `@[spec_of <kind> "crate::fn"]`; the theorem
that discharges one is tagged `@[proves <spec>]`. Everything below is stated
and typechecks; every proof is currently `sorry`.

| Spec | Kind | Statement | Theorem (sorry) |
|---|---|---|---|
| `ByteEcho.Spec.ByteEchoSpec` | total | For every input byte, `byte_echo` terminates and writes exactly that byte. | `ByteEcho.Proof.byte_echo_correct` |
| `GcdStdio.Spec.KernelSpecification` | total, internal | The out-of-line `gcd_u64` kernel (`func1`), run on two `i64`s, returns `Nat.gcd`. | `GcdStdio.Proof.kernel_correct` |
| `GcdStdio.Spec.PublicEntrySpecification` | total | For every pair of `u64`, `gcd` terminates and writes their `Nat.gcd`. | `GcdStdio.Proof.gcd_correct` |
| `Mergesort.Spec.PublicEntrySpecification` | partial | Every finite run of `mergesort` on packed `u32`s either traps with the allocator's `talos.oom` or returns a sorted permutation of the input. Termination is not claimed. | `Mergesort.Proof.mergesort_correct` |

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
```

`Programs.Smoke.runBytes` is the small driver: it instantiates a module under
`Universal.envFor` (every host the interpreter knows, resolved by import name),
feeds it an input byte list and returns the output byte list. It is the seed
of a harness for running these programs, and later NEAR contracts, as tests.

The interpreter's CLI `runner` cannot run these programs: it rejects any module
with imports.
