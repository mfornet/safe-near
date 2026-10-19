# Repository tools

Run `just` at the repository root for the documented command list.

| Command | Purpose |
| --- | --- |
| `just check-toolchains` | Check every owned Lake package against the root `lean-toolchain` |
| `just lean-lint` | Check all owned Lean files with pinned Mathlib text-based style linters |
| `just lean-format` | Apply Mathlib's automatic style fixes, then check remaining findings |
| `just wasm-test [pattern]` | Run all official Wasm tests or filter their filenames |
| `just wasm-summary` | Summarize the committed Wasm coverage report |
| `just wasm-report` | Regenerate that report using the pinned wasm-tools |
| `just programs-test` | Build the example programs and run smoke and regression harnesses |
| `just programs-build` | Rebuild Rust program Wasm and WAT |
| `just audit near-lean/wasm` | Check a package's transitive proof axioms |
| `just tools-test` | Run offline Python tooling regression tests |
| `just snapshot /tmp/fixture.json lockup.near` | Download a block-pinned account fixture |
| `just snapshot-vm SNAPSHOT ACCOUNT SCENARIO --report REPORT` | Compare VM calls seeded from a complete captured account |

## Lean quality

`lean-toolchain` at the repository root is the canonical release pin. Each
repository-owned Lake package also carries that pin so it works independently.
`check_lean_toolchains.py` discovers Lake manifests and pins through Git,
including newly added local files. Submodules and ignored build dependencies
are outside its scope. When upgrading Lean, update all pins together.

The Lean quality workflow runs the pin check, tool tests, and source-style
checks. The style driver uses the Mathlib revision in the Wasm package's
committed Lake manifest. It checks line endings, trailing whitespace,
adaptation-note conventions, and Unicode conventions. Automatic fixes cover
the subset Mathlib can repair; unresolved findings still fail the command.
This is source-style formatting, not a complete syntax layout formatter.
The text-only semicolon rule is disabled because it matches meaningful WAT
string literals in interpreter tests.

After a fresh checkout, prepare the style dependency once:

```sh
cd near-lean/wasm
lake exe cache get
lake build +Mathlib.Tactic.Linter.TextBased
```

Then run `just lean-lint` or `just lean-format` from the repository root.
To check selected files, use `python3 tools/lean_style.py path/to/File.lean`.
The driver never formats submodule sources, ignored dependencies, or human notes.

`python3 tools/tests/check_lean_style.py` exercises the real Lean checker:
check mode must leave a dirty fixture unchanged, formatting must be repeatable,
and WAT string literals must remain intact. These checks run separately from
the Python tests because they need the pinned Lean/Mathlib installation.

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
