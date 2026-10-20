# Repository tools

Run `just` at the repository root for the documented command list.
`just test-all` runs the executable suites; `just check` adds source checks,
core axiom audits, formatter integration checks and contract builds.

| Command | Purpose |
| --- | --- |
| `just test-all` | Run programs, NEAR scenarios, official Wasm tests and exact VM conformance |
| `just chain-replay-test` | Exercise trusted JSON block replay and complete-state continuation |
| `just audit-all` | Audit all core packages and list the programs' open proofs |
| `just check` | Run the combined repository checks |
| `just check-toolchains` | Check every owned Lake package against the root `lean-toolchain` |
| `just vm-dependencies` | Check Lean's actual VM import closure for legacy interpreters and proof APIs |
| `just lean-lint` | Check all owned Lean files with pinned Mathlib text-based style linters |
| `just lean-format [files...]` | Apply validated syntax formatting to handwritten package sources |
| `just lean-format-check [files...]` | Check canonical syntax layout without writing files |
| `just lean-format-diff [files...]` | Preview syntax formatting as a patch |
| `just lean-style-fix` | Apply Mathlib's automatic text-style fixes |
| `just wasm-test [pattern]` | Run all official Wasm tests or filter their filenames |
| `just wasm-summary` | Summarize the committed Wasm coverage report |
| `just wasm-report` | Regenerate that report using the pinned wasm-tools |
| `just programs-test` | Build the example programs and run smoke and regression harnesses |
| `just programs-build` | Rebuild Rust program Wasm and WAT |
| `just audit near-lean/wasm` | Check a package's transitive proof axioms |
| `just tools-test` | Run offline Python tooling regression tests |
| `just snapshot /tmp/fixture.json lockup.near` | Download a block-pinned account fixture |
| `just snapshot-vm SNAPSHOT ACCOUNT SCENARIO --report REPORT` | Compare VM calls seeded from a complete captured account |
| `just chain-reference-build [options...]` | Build the clean pinned nearcore transaction/receipt reference |
| `just chain-import SNAPSHOT DESTINATION [--scenario SCENARIO]` | Prepare matching synthetic chain genesis from complete captured accounts |
| `just chain-compare FIXTURE [options...]` | Compare represented per-block contract state, receipts, outcomes and fees |
| `just chain-version-test` | Compare signed V0/V1 batches, rejected nonces and protocol gates |
| `just chain-chunk-storage-test` | Compare chunk cache, commit/rollback and scheduler boundaries |
| `just chain-contract-test` | Compare native callback delivery and exact chunk-trie storage gas |
| `just chain-contract-probe [options...]` | Report the full contract corpus, including known failing trie-gas comparisons |
| `just chain-import-test` | Check native state encoding, captured-state imports and deterministic signing |
| `just chain-reference-test [options...]` | Exercise the native reference's chunk boundaries and complete raw-state replay |

## Lean quality

`lean-toolchain` at the repository root is the canonical release pin. Each
repository-owned Lake package also carries that pin so it works independently.
`check_lean_toolchains.py` discovers Lake manifests and pins through Git,
including newly added local files. Submodules and ignored build dependencies
are outside its scope. When upgrading Lean, update all pins together.

The Lean quality workflow runs the pin check, tool tests, source-style checks,
and syntax-formatting checks for the two new program harness modules.
The text-style driver uses the Mathlib revision in the Wasm package's
committed Lake manifest. It checks line endings, trailing whitespace,
adaptation-note conventions, and Unicode conventions. Automatic fixes cover
the subset Mathlib can repair; unresolved findings still fail the command.
The text-only semicolon rule is disabled because it matches meaningful WAT
string literals in interpreter tests.

Unicode conventions apply to source notation and comments; string, raw-string
and character literal contents are opaque contract data. A lexical scan masks
those contents for the code-point check, preserving source line numbers and
handling escapes and nested comments. Unicode findings outside literals remain
errors and are never automatically replaced. This preserves multilingual ABI
test data while retaining source-notation checks.

After a fresh checkout, prepare the style dependency once:

```sh
cd near-lean/wasm
lake exe cache get
lake build +Mathlib.Tactic.Linter.TextBased
```

Then run `just lean-lint` or `just lean-style-fix` from the repository root.
To check selected files, use `python3 tools/lean_style.py path/to/File.lean`.
The driver never formats submodule sources, ignored dependencies, or human notes.

`python3 tools/tests/check_lean_style.py` exercises the real Lean checker:
check mode must leave a dirty fixture unchanged, formatting must be repeatable,
and WAT string literals must remain intact. These checks run separately from
the Python tests because they need the pinned Lean/Mathlib installation.

## Syntax formatting

`lean_format.py` builds [lean-fmt](https://github.com/jcreinhold/lean-fmt) from
the immutable revision recorded in `lean_format_tool.json`, using the exact
compiler in the root `lean-toolchain`. The pinned sources are from the
`v4.34.0-rc2` release and are tested here with Lean `v4.34.1`; the upstream
toolchain file is not used to choose our compiler. A future compiler or
formatter upgrade must pass the same integration checks.

The first invocation fetches and builds the tool into the ignored
`near-lean/.lake/lean-fmt/` cache. Later invocations verify the source revision
and reuse the build. Interrupted downloads never publish a partial checkout.
`lean-fmt.toml` sets the shared layout margin. Candidate validation always
runs; this wrapper exposes no validation bypass.

```sh
just lean-format-diff near-lean/programs/lean/Programs/Harness.lean
just lean-format near-lean/programs/lean/Programs/Harness.lean
just lean-format-check near-lean/programs/lean/Programs/Harness.lean
```

With no filenames, the command selects all handwritten sources in all owned
Lake packages. Build a package's dependencies before formatting its files.
Human notes, generated `Program.lean` AST files, ignored dependencies and
submodule sources are protected from selection. Standalone tooling scripts
outside Lake packages remain covered by `lean-lint`.

CI currently enforces canonical syntax layout for `Programs/Harness.lean`
and `Programs/Regression.lean`. Existing package sources still have layout
debt: `just lean-format-check` reports it rather than hiding it behind a
baseline. Expanding enforcement is a separate source-formatting change, so
formatting the new harness does not also rewrite existing contract proofs.

`python3 tools/tests/check_lean_format.py` checks the real formatter against a
tiny independent Lake package: check mode preserves dirty bytes, formatting
preserves comments and string literals, a second pass is stable, and the
formatted theorem still builds with the kernel. Pure Python selection tests
also verify nested package ownership, protected inputs, ignored dependencies,
and failure when a formatter process is killed.

## Combined checks

`just test-all` runs the toolchain check and Python tooling/conformance-driver
tests, native Rust unit tests, program smoke/regression tests,
VM/runtime/chain scenarios, the wNEAR adapter suite,
the complete official Wasm testsuite, and strict VM conformance against the
pinned Rust oracle. It stops on the first failing command. Install the Lean,
Rust and pinned wasm-tools prerequisites documented by those components first.

`just check` adds Mathlib text-style checks, core axiom audits, builds of every
contract verification package, and both formatter integration tests. It uses
the same two-file syntax-layout enforcement as CI. Broader layout debt is
reported separately by `just lean-format-check`.

The core axiom audit tolerates `sorryAx` only in the Programs package and
prints those open declarations. It resolves every audited module from the
selected package's own compiled artifacts before searching dependencies and
fails if a local artifact is missing. This matters for overlapping executable
names such as `Tests.Main`, including case aliases on macOS. A real-Lean
regression proves that a dependency's same-named module cannot hide a local
nonstandard axiom; `just audit-all` and CI run that regression.
Contract builds may report open proofs as warnings; a successful build is not
a claim that those contracts are verified.

## VM execution dependency boundary

`Interpreter.Wasm.Operations` holds the shared numeric and GC operations.
Both interpreter implementations use those same definitions. `SmallStep`
imports that executable layer directly; `Semantics` retains the legacy
big-step interpreter for regression tests and the existing proof API.
`NearVM.State` imports only host types and `NearVM.Run` explicitly imports
the small-step machine. Executing the VM does not need the broad Wasm proof
umbrella.
The compiler-header report records the current execution dependency graph in
`audit/vm-dependencies.json`. New runtime modules may extend that graph while
the legacy interpreter and proof API boundary stays enforced.

`check_vm_dependencies.py` builds `NearVM`, then inspects Lean's imported-module
header. It rejects legacy `Semantics`, `Wp`, `Spec` and CodeLib imports,
including indirect imports, and requires the actual small-step/operation
modules to be present. CI runs it after building the VM. Its separate Lean
fixture test demonstrates a clean graph, a forbidden transitive dependency,
and an incorrectly disconnected execution module.
`just vm-dependencies` runs both the real graph check and those adversarial
fixture cases; `just check` includes the same gate.

## Full runtime reference

The full transaction/receipt reference is documented in
[chain-conformance/README.md](chain-conformance/README.md). It runs the actual
trie-backed `Runtime::apply` and preserves complete raw state. Its smoke checks
do not yet compare the Lean chain runner with nearcore.

## Snapshots

See [SNAPSHOTS.md](SNAPSHOTS.md) for format, trust boundary, prefix-filtered
storage, provider size limits, and historical captures. A live full capture of
`lockup.near`, including 522,447 bytes of deployed code, succeeded at block
`GXdjU1zVDi5HJNh2YmnTEWiqGPZA2b4iegU28kVvXhpn` (height 220701709,
protocol 86). Capturing that same hash again produced byte-identical JSON.

[SNAPSHOT_VM.md](SNAPSHOT_VM.md) explains how to feed a complete captured
account to compatible reference and model executables, preserving the actual
contract identity and block context. The adapter freezes executables and
configuration before running, allowing the components to live in separate
worktrees while other agents continue rebuilding them.

The Lean chain replay wire format and its external decoder assumptions are documented in
[`chain-conformance/REPLAY.md`](chain-conformance/REPLAY.md). Its tests run in
`just test-all` and CI; the native/Lean comparison bridge remains open.

`just chain-gas-test` runs the targeted native/Lean transfer and account-creation
gas regression after the reference is built. It records all field differences
and explicit observation gaps; it does not establish general runtime conformance.

Complete captured accounts can now seed both chain executors with `just chain-import`.
See [chain-conformance/SNAPSHOTS.md](chain-conformance/SNAPSHOTS.md) for explicit
synthetic callers, signed actions, fixture evidence and supported scope.
