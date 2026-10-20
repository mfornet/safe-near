# Periodic check — 2026-10-20

Checked starting commit `dbf9d11` on macOS/Apple Silicon. Initial tree was clean.
All required commands and additional CI checks passed locally. Remaining findings
are documented below; hosted CI for that starting revision was blocked externally.

After this check, merged remote `main` at `fc34915`. The counts and expensive
conformance results below describe the checked starting revision plus its check
fixes. They are historical evidence, not measurements of the newer merged main.
See [merge follow-up](merge-follow-up.md) for conflict resolutions and validation.

## 1. Build and tests — passed, with recorded tool warnings

- VM/runtime/chain: **65 / 139 / 25** scenario checks passed; **65** adapter checks passed.
- Independent VM/finance/nonce/allowance comparisons: **350 / 72 / 126 / 66** passed,
  **zero differences** (614 total).
- The **65,142-line** Wasm testsuite report exactly matches the committed CI baseline.
- wNEAR rebuilt byte for byte to `DL2f5xmZ44cQRP6vBMt94rvseH5d5KKnAGis2WkTAsh1`.
  Only its reproduction date changed. Program binaries/WAT and regenerated configs
  are unchanged.
- All seven packages rebuilt; completed proof packages passed with warnings treated
  as errors. The program package retains its four known proof holes.

**Recorded:** clean pinned nearcore emits a `wasmparser 0.78.2` future-compatibility
warning; plasTeX emits four fallback-renderer warnings for generated macro setup.
Changing the required reference lockfile or adding a renderer shim solely to hide
warnings was deferred. Generated blueprint labels and proof markers were verified.

## 2. Trusted base — no growth

Source counts (comments/strings excluded), unchanged from the starting checkout:

| Package | sorry | partial | maxHeartbeats |
|---|---:|---:|---:|
| `contracts/w-near/verification` | 0 | 0 | 0 |
| `near-lean/chain` | 0 | 0 | 0 |
| `near-lean/iris-wasm` | 0 | 0 | 47 |
| `near-lean/programs/lean` | 4 | 0 | 0 |
| `near-lean/runtime` | 0 | 0 | 1 |
| `near-lean/vm` | 0 | 0 | 8 |
| `near-lean/wasm` | 0 | 6 | 16 |
| **Total** | **4** | **6** | **72** |

`axiom`, `native_decide`, `unsafe`, `implemented_by`, and explicit `opaque`:
**zero code occurrences**. Other dataset contracts have no verification project.
All seven transitive audits passed, covering all **356 modules / 44,901 declarations /
27,044 theorems**; only the programs package tolerates its known
`sorryAx` dependencies. wNEAR: **1,357 declarations / 670 theorems / zero violations**.
Conventional interpreter/adapter/oracle/config fidelity assumptions did not grow.
See [axiom summary](axiom-summary.json) and [source inventory](trusted-source.json).

## 3. Pins — deliberately retained

All seven Lean toolchains agree on **4.34.1**; Mathlib/Iris/LeanArchitect and other
Lake revisions remain fixed. nearcore remains **44f7ae6… / 2.13.4**; reference Rust
pins remain **1.93.0 / 1.93.1**, program Rust **1.95.0**, historical wNEAR Rust
**1.51.0**, wasm-tools **1.251.0**. All 11 binary/hash/metadata hashes match.

**Recorded:** Lean/Mathlib 4.35 and newer Actions majors are available. Keep the
coordinated Lean baseline and defer major Actions migrations until hosted CI can
validate them. [Full pin inventory and per-pin decisions](pins.json), including
all 12 gitlinks and contract source/build pins.

## 4. Dead/duplicated code — fixed / recorded

**Fixed:** removed six unreferenced helpers and the completed root TODO. Full
affected builds passed. No dead module or tool was established.

**Recorded:** both duplicated NEAR hosts remain active with different state types
and proofs; consolidation needs a coordinated proof port. Tiny test-local helpers
remain because adding a shared dependency would not simplify them.

## 5. Documentation — fixed

**Fixed:** stale external paths, comments/help, proof warnings, and misleading
blueprint claims. The blueprint contains exactly **15 spec nodes / 13 completed
proof endpoints**; deployed refinement remains open. Removed handwritten goals
without formal counterparts. Rebuilds now clear stale generated HTML pages.
Both `sorries` recipes use the real transitive audit and propagate build failures.
All eight Spec modules are unchanged outside comments/whitespace.

**Fixed after user authorization:** removed the notes editing restriction and
[reconciled stale notes](notes-reconciliation.md), including consolidating the
numbered proving-policy copy. Remaining goals are explicitly marked as future work.

## 6. CI health — fixed / externally blocked

**Fixed:** recipe/interpreter path-trigger gaps and incomplete shared dependency
cache keys. Both workflows parse successfully.

**Handed to human:** [all five starting-commit jobs](ci-jobs.json) were prevented
from starting by GitHub's billing/spending-limit check. Hosted green status cannot
be confirmed until that is resolved. No previous report exists to compare timings.
[Detailed review](review-detail.md) records slow modules, retained heartbeat
settings, job timeout observations, and [individual final build timings](final-build-timings.json).

## 7. Cost

Measured command wall time: **3585.31 seconds (59.8 minutes)**,
including proof-fix retries and final rebuilds; excludes setup and review time.
One coordinator and three delegated agents were used (Luna for pin/CI inventory).
**Total token/dollar cost is unavailable:** the agent tools expose no per-run
billing telemetry. It is not reported as zero. This report establishes the first
repository baseline for later checks.
