# Periodic check detail — 2026-10-20

Status: command matrix complete.

Starting checkout: `dbf9d11003449a8cc1cd25340bb37873187f6c18`; initially clean.
Local platform: macOS, Apple Silicon. This is the first dated report found in
the repository; there is no previous report for trend or doubling comparisons.

## 1. Build and tests

Command outcomes and measured wall seconds are retained in `results.json`,
`extra-results.json`, and `proof-cleanup-results.json`. Verbose local logs are
in `logs/` (ignored); conformance/axiom evidence is regenerated under `audit/`.

| Command group | Result | Wall seconds |
|---|---|---:|
| `build-all` | pass | 379.19 |
| `near-build` | pass | 698.04 |
| `near-test` | pass | 268.45 |
| `runtime-adapter-test` | pass | 20.35 |
| `near-conformance` | pass | 123.45 |
| `finance` | pass | 15.64 |
| `nonce` | pass | 10.56 |
| `allowance` | pass | 8.58 |
| `wnear-audit` | pass | 49.53 |
| `blueprint` | pass | 24.55 |
| `reproduce` | pass | 97.84 |
| `wasm-report` | pass | 140.81 |
| `sorries` | pass | 43.95 |
| `wasm-ci` | pass | 209.98 |
| `wasm-smoke` | pass | 2.54 |
| `iris-build` | pass | 223.31 |
| `programs-build` | pass | 310.47 |
| `wasm-audit` | pass | 273.22 |
| `iris-audit` | pass | 57.44 |
| `programs-audit` | pass | 87.82 |
| `vm-audit` | pass | 79.43 |
| `runtime-audit` | pass | 311.32 |
| `chain-audit` | pass | 34.81 |
| `programs-reproduce` | pass | 1.48 |
| `config-regenerate` | pass | 7.37 |

The initial contract build passed with 24 warning diagnostics. Cleanup removed
unused simp arguments/tactics, replaced deprecated names, and made incomplete
aesop search fall back explicitly to arithmetic; `lake build Model Proofs --wfail` then passed without warnings (8.68 s).
Its two intermediate failed adjustments and successful retry cost 39.47 s.
The comparator's four Python unit tests passed. Both `sorries` entry points also
correctly rejected a simulated Lake exit 23 and never printed a false clean result
(`sorries-failure-check.json`).

**Recorded tool warnings:** pinned nearcore's `wasmparser 0.78.2` reports a future
Rust incompatibility (semicolon in expression-position macro,
`operators_validator.rs:45`, Rust issue #79813). Its required clean checkout and
lockfile remain intact; patching/upgrading it would change the reference. The
blueprint renderer reports four fallbacks for generated TeX setup commands
(`makeatletter`, `providecommand`, `makeatother`, `gdef`). HTML labels and proof
markers were checked (`blueprint-check.json`); no theorem content is missing.
Retained these upstream-tool warnings rather than modifying generated code or
introducing a renderer shim solely to suppress them.

## 2. Trusted base

Source-token counts exclude nested comments and strings across 356 tracked Lean
files. Counts match the starting checkout; no new trust mechanism was introduced.
`axiom`, `native_decide`, `unsafe`, `implemented_by`, and `opaque` all have zero
code occurrences. Exact locations are in `trusted-source.json`.

| Package / contract | sorry | partial | maxHeartbeats settings |
|---|---:|---:|---:|
| `contracts/w-near/verification` | 0 | 0 | 0 |
| `near-lean/chain` | 0 | 0 | 0 |
| `near-lean/iris-wasm` | 0 | 0 | 47 |
| `near-lean/programs/lean` | 4 | 0 | 0 |
| `near-lean/runtime` | 0 | 0 | 1 |
| `near-lean/vm` | 0 | 0 | 8 |
| `near-lean/wasm` | 0 | 6 | 16 |
| **Total** | **4** | **6** | **72** |

The other ten contract entries have no Lean verification project; a zero source
count there is not a verification claim. The four known holes are
`Programs.ByteEcho.Proof.byte_echo_correct`,
`Programs.GcdStdio.Proof.kernel_correct`,
`Programs.GcdStdio.Proof.gcd_correct`, and
`Programs.Mergesort.Proof.mergesort_correct`. They remain intentionally open;
this check does not implement new program proofs.

Transitive audits (the three standard axioms are allowed):

| Package | Modules | Declarations | Theorems | Nonstandard axiom dependencies |
|---|---:|---:|---:|---:|
| `wnear` | 27 | 1357 | 670 | 0 |
| `wasm` | 87 | 26314 | 16681 | 0 |
| `iris-wasm` | 87 | 8225 | 5327 | 0 |
| `programs` | 11 | 308 | 41 | 4 |
| `vm` | 70 | 5512 | 2695 | 0 |
| `runtime` | 65 | 2930 | 1558 | 0 |
| `chain` | 9 | 255 | 72 | 0 |

The interpreter/decoder and VM semantics, wNEAR encoding/receipt adapter,
reference normalization/comparison scripts, and config dumper remain conventional
fidelity boundaries. Tests check finite cases; they do not establish complete
nearcore equivalence or deployed-binary refinement. Those interfaces did not grow.
VM conformance uses locked published `near-vm-runner 0.37.4`; finance, nonce and
allowance use the clean pinned checkout. These are distinct reference seams.
Published reference crates explicitly retain their `dirty=true` provenance caveat
in `near-lean/runtime/reference.json`; equality with clean nearcore is not assumed.

## 3. Pinned versions — deliberately retained

Full seven-toolchain/Lake manifest inventory, contract hashes, lockfile SHA256s,
Actions versions, and upstream release observations are in `pins.json`.

- All seven Lean toolchains are `4.34.1`; Mathlib is `v4.34.1`
  (`d13f23b723b8a846827a245b89c10fc7d3f11612`). Iris remains
  `04b7689c294bb1dd6401e2dd53b337871934ea47`; LeanArchitect remains
  `468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`. Keep these and every other
  recorded Lake revision together. [Lean 4.35.0](https://github.com/leanprover/lean4/releases/tag/v4.35.0)
  and [Mathlib 4.35.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0)
  are available; their coordinated migration is deferred to preserve this checked baseline.
- nearcore remains `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, matching both
  adapter builders, CI and the clean local reference checkout.
  [2.13.4](https://github.com/near/nearcore/releases/tag/2.13.4) is still the latest
  upstream release observed. Published oracle/config crates remain `0.37.4`.
- Rust remains `1.93.0` for clean-nearcore adapters, `1.93.1` for VM conformance,
  `1.95.0` for program Wasm, and Docker `rust:1.51.0` for the historical wNEAR
  rebuild. Keep these purpose-specific pins for reference and binary reproducibility.
  wasm-tools remains `1.251.0`, paired with committed decoder/tests output.
- Actions remain checkout/cache `v5`, upload-artifact `v4`, lean-action `v1`,
  rust-cache/install-action `v2`, and the stated Rust toolchain tags.
  Newer majors exist: [checkout v7.0.1](https://github.com/actions/checkout/releases/tag/v7.0.1),
  [cache v6.1.0](https://github.com/actions/cache/releases/tag/v6.1.0),
  [upload-artifact v7.0.2](https://github.com/actions/upload-artifact/releases/tag/v7.0.2).
  Record this drift; defer major workflow migrations until hosted CI can run.
  Major Action tags remain mutable references, an existing limitation.
- All 11 committed binaries match both `hash.txt` and `contract.toml` code hashes
  (`contract-hashes.json`). Keep every historical on-chain/source/build pin.
  Reproduction may refresh the wNEAR check date; that is evidence metadata, not a pin change.

## 4. Dead and duplicated code

**Fixed:** deleted six unreferenced helpers after exact workspace-name and attribute
review: `unwrapBalance_ok`, `copyWordsInnerFrame`, `fillWordsInnerFrame`,
`checkReceiver`, `registerLen?`, and the private `stripComments` wrapper.
Active `stripCommentsAux` remains. Deleted the completed root `todo.md`.
No dead module or tool was established: apparent orphans are explicit Lake roots
or executable entrypoints, and `test_compare.py` is discovered by unittest.
Committed Wasm/WAT fixtures are reproducibility inputs, not stray build output.

**Recorded:** `NearVM` and `CodeLib.Near` duplicate state, memory and host helpers.
Both hosts are active and their state types/proofs have diverged; deleting either
would break builds. Consolidation requires a coordinated proof port rather than
an isolated helper deletion. Small package-local test `check` functions remain:
a new shared dependency would add more structure than it removes. Single-use
public theorem endpoints are not classified as dead merely by reference counts.

## 5. Documentation and comments

**Fixed:** obsolete `docs/human`/dataset paths, dataset verification layout,
proof-status/blueprint command help, inaccurate IEEE32 axiom-root comments,
and stale functional-host promise/crypto/fuel descriptions. CodeLib umbrella
and attribute comments now distinguish the copied upstream Talos extractor
contract from the tools actually present here.

The blueprint now includes all 15 annotated proposition specifications and their
13 completed proof endpoints. `Refines` and `RefinesNearLean` remain open
propositions. Removed five handwritten theorem environments with no corresponding
formal theorem; removed informal chain goals from the blueprint, retaining
future-chain-specification status in the verification README. A legend explains
that a check mark on a definition formalizes its statement, not a proof of it.
The web recipe now clears generated HTML so removed chapters cannot survive
as stale pages.
Corrected runtime/chain existence, callback unused-amount semantics, unverified
upgrade claims, and the distinction between implemented adapters and proved
serialization/refinement. The refinement annotation now describes its existing
funded-resource/callback premises and accounting/rollback conclusions. The formal
Lean specification expressions were not changed (`spec-stability.json`).

**Fixed after user authorization:** removed the notes editing restriction and
applied the stale-documentation findings. See
[notes-reconciliation.md](notes-reconciliation.md) for the resolved items,
including consolidation of the numbered proving-policy copy.
Inline comments were reviewed by targeted stale-path/TODO/semantic searches;
this was not a proof-by-proof semantic review of every source file.

## 6. CI health and timings

**Fixed:** both workflows now trigger on `justfile`; runtime-reference also
triggers when its interpreter dependency changes. Wasm's shared cache includes
the nested programs manifest, and runtime/conformance caches cover nested
manifests and the contract verification toolchain/manifest.
All remaining directories are covered by their applicable workflows; unrelated
dataset entries have no verification jobs. No empty CI step was established.

**Handed to human:** all five jobs for the starting main commit failed before
executing any steps because GitHub reports failed account payments or an exhausted
spending limit. [Wasm run](https://github.com/mfornet/safe-near/actions/runs/39406104763),
[runtime-reference run](https://github.com/mfornet/safe-near/actions/runs/39406104791).
`ci-jobs.json` retains the exact annotations. Their metadata shows roughly two
seconds per job, which is not a build-time measurement. CI green status cannot
be confirmed until the account issue is corrected. Runtime-reference has a
60-minute timeout; other jobs use GitHub's default timeout. No historical timing
baseline permits a doubling claim.

Largest local elaborations observed (seconds; cold/rebuild context matters):

| Module | Seconds |
|---|---:|
| `Interpreter.Wasm.SmallStep` | 156 |
| `Interpreter.Wasm.Examples.SegmentOffsetExpr` | 124 |
| `Interpreter.Wasm.Examples.SegmentOffsetExpr` | 120 |
| `Interpreter.Wasm.Examples.GlobalInitExpr` | 88 |
| `Interpreter.Wasm.Examples.Validation` | 84 |
| `Interpreter.Wasm.Examples.SmallStep` | 84 |
| `Interpreter.Wasm.Examples.GlobalInitExpr` | 84 |
| `Interpreter.Wasm.Examples.Validation` | 81 |
| `CodeLib.Near.Examples.KvSetter` | 77 |
| `Interpreter.Wasm.Decoder.ProofEval` | 76 |

These and the 72 raised heartbeat settings are recorded simplification candidates.
No heartbeat budget was raised. Reducing proof/search cost without a semantic
change requires targeted follow-up; this check retained the successful proofs.
Recipe wall times include each group's builds and tests. Initial project-cold
per-package Lake timings were not independently instrumented (pinned dependency
artifacts were reused). Final individual package build wall times are measured
separately in `final-build-timings.json`:

| Package | Seconds | Result |
|---|---:|---|
| `near-lean/wasm` | 2.54 | pass |
| `near-lean/vm` | 2.51 | pass |
| `near-lean/runtime` | 2.62 | pass |
| `near-lean/chain` | 2.61 | pass |
| `near-lean/iris-wasm` | 2.31 | pass |
| `near-lean/programs/lean` | 2.31 | pass |
| `contracts/w-near/verification` | 2.83 | pass |
| `all contracts` | 2.82 | pass |

Native C compilation also took 235 seconds for `Interpreter.Wasm.Semantics`
and 234 seconds for `CodeLib.Examples.Quicksort`; these are compiler costs, not
Lean proof elaboration. Generated programs re-export the broad CodeLib umbrella,
which includes worked examples, so smoke builds pull in that native dependency.
Narrowing the documented proof surface or separating its library is recorded
follow-up, rather than an unverified late API refactor. Local timings depend on host load.

## 7. Cost and follow-up

Measured command wall time: **3585.31 seconds** (includes the three
proof-cleanup attempts, final blueprint rebuilds and individual package builds; excludes setup, review, and the four tiny Python tests).
One coordinator and three delegated agents were used; the mechanical pin/CI
inventory used the cheaper Luna model. Token and dollar telemetry is not exposed
by these agent tools, so a total token/dollar cost is **unavailable**, not zero.
No prior report exists for a cost comparison. Future runs should capture that
telemetry at the host if available.

Cache preparation initially overlapped two builds; those attempts were stopped
and the logged sequential build was restarted. No finding was accepted as fixed
on the strength of the interrupted attempts. Verbose copied-cache setup logs were
not retained. Maintainer follow-up is CI billing and later deliberate
dependency/host-consolidation work recorded above.
