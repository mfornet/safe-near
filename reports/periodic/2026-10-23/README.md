# Periodic check — 2026-10-23

Checked `origin/main` at `eea6053` (97 commits since the last check at
`dbf9d11`), on x86_64 Linux in a Claude Code cloud session, with nearcore
cloned clean at the pin `44f7ae6` (2.13.4). The tree was clean. All fixes are
commits on `claude/periodic-check-8n2hzf`; the final section 1 run was at the
head of that branch.

Sections run (due): `build`, `trusted-base`, `dead-code`, `simplification`
(first time), `divergence` (first time), `docs`, `tests-ci`, `features` (first
time). Skipped as not due: `pins` (checked 2026-10-20, within its 7 days).

**Linear:** this session had no Linear connector or API key, so the unfixed
findings are drafted in [linear-drafts.md](linear-drafts.md) (31 drafts:
9 `divergence`, 7 `missing-feature`, 6 `simplification`, 5 `test-coverage`,
4 `stale`) instead of filed. **Maintainer action:** file them (searching open
`periodic-check` issues first), then add the IDs to the ledger with
`--record ... --issue`.

## 1. Build and tests — four failures found and fixed

`just periodic-check` (78 steps) at the branch head: SECTION1_RESULT

Failures found on `main`, each fixed before continuing:

1. **`near-lean/chain` did not build.** `ChainReplay/Encode.lean:27` had no case
   for `Action.useGlobalContract`, added in 62fbab7. Nothing automatic builds
   the chain package, so it went unnoticed. Fixed by encoding the action as the
   VM's conformance encoder already does, and documented in
   `tools/chain-conformance/REPLAY.md` (5391ce3).
2. **The Wasm testsuite report failed when run from the repository root** (as
   CI's `wasm.yml` and the periodic plan do): the driver reads
   `vendor/testsuite` and `testsuite_out_of_scope.txt` relative to the working
   directory. `scripts/suite.sh` now runs it from the package directory
   (3fdf34d). The regenerated report is byte-identical to the committed one
   (zero `fail`).
3. **VM conformance diverged on x86_64 Linux (50 of 400).** Configs for v69,
   v70 and v83 name NearVm, which `near-parameters` keeps on x86_64; the oracle
   is built with only the default `wasmtime_vm` engine, so
   `near_vm_runner::prepare` panicked. The last check ran on Apple Silicon,
   where the swap to Wasmtime is implicit. The adapter now pins Wasmtime on
   every host (2941d45): **400 passed, 0 differed** (350 last time; 50 new
   scenarios).
4. **Environment only:** the style check needs `lake build
   +Mathlib.Tactic.Linter.TextBased` once (documented in `tools/README.md`), and
   the nearcore reference builds need about 8 GB of disk each; the first runs
   failed on both. No repository change.

## 2. Trusted base — down, one explained increase

Source counts with comments and strings stripped (previous → now):

| Package | sorry | partial | maxHeartbeats |
|---|---:|---:|---:|
| `contracts/w-near/verification` | 0 → **1** | 0 | 0 |
| `contracts/sputnik-dao-factory/verification` (new) | 0 | 0 | 0 |
| `contracts/sputnikdao2-v3.2/verification` (new) | 0 | 0 | 0 |
| `near-lean/wasm` | 0 | 6 → 0 | 16 → 3 |
| `near-lean/wasm-logic` (new) | 0 | 0 | 0 |
| `near-lean/interface` (new) | 0 | 0 | 0 |
| `near-lean/vm` | 0 | 0 | 8 → 4 |
| `near-lean/runtime` | 0 | 0 | 1 |
| `near-lean/chain` | 0 | 0 | 0 |
| `near-lean/iris-wasm`, `near-lean/programs` (removed in 5713333) | 0, 4 → — | 0 | 47, 0 → — |
| **Total** | **4 → 1** | **6 → 0** | **72 → 8** |

`axiom`, `native_decide`, `unsafe`, `implemented_by` and bodiless `opaque`:
zero at both revisions. The only increase is the wNEAR `sorry`:
`refines_wnear_exported` (`Proofs/Refinement.lean:87`), the deliberately open
deployed-binary refinement for the 15 exported methods (d766e10); the audit
tolerates `sorryAx` in `Proofs.Refinement` alone. The one unbounded budget,
`maxHeartbeats 0` at `near-lean/vm/NearVM/Metered.lean:897`, predates the range
(draft S1).

Trusted by convention: the Wasm interpreter was rewritten clean-room
(5713333; 126 files) and passes the in-scope spec testsuite with zero failures;
39 multi-memory files are skipped as out of scope (`testsuite_out_of_scope.txt`,
documented). `tools/axiom-audit.py` was rewritten; its regression test injects
an axiom that must be caught. No new trust assumption without a note.

## 3. Pins — not due

Checked 2026-10-20. This check changed none (the oracle fix in section 1 keeps
`tools/runtime-conformance/Cargo.lock`).

## 4. Dead and duplicated code — fixed / filed

**Fixed** (8b0380f, rebuilt in section 1): removed `contextRegisterFn`
(`NearVM/Host.lean`), `bytes64` (`WasmLogic/Resources.lean`), `importedFuncs`
(`Wasm/Syntax.lean`) and `checkValType` (`Wasm/Validate.lean`), each referenced
only at its definition.

**Kept:** `runLastProposalIdView`, `runLastBountyIdView`, `runActionsLogView`
and `wirePolicyOrdered` in the in-progress sputnikdao2-v3.2 model (likely
planned symmetry wrappers); `ScheduleSupported`/`DeliveryFair` in
`NearChain/History.lean` (spec vocabulary).

**Filed:** orphan `NearRuntime/TrieAccounting.lean` (X1); duplicated encoding
primitives in runtime (S5). Low value, not filed: identical test `check`
helpers in the three test mains, `finalCells`/`mainConfig` in two wasm-logic
examples, `run_case` and a subprocess `run` copied across conformance scripts.
No stray files; every recipe, script and CI path resolves.

## 5. Simplification and compile cost — fixed / filed

The previous timings could not rank modules (no-op rebuilds, and the module
table named deleted packages), so a fresh `near-lean/vm` build was timed:
DepositRegistry 105 s, Metered 72, ActionReservations 69, HostGasLimits 67,
HostGasFloor 64, HostDeposits 62, MeteredSelection / MeteredBatchReservations /
HostDispatch 55, PromiseEncoding 50.

**Fixed** (8b0380f): `HostGas.lean` and `HostNeutralDeposits.lean` repeated one
`dsimp only [...]; repeat (first | ...)` block 48 and 43 times; a `local macro`
per file expands to the same text (−847/+116 lines). No statement changed.

**Filed:** S1 (`maxHeartbeats 0`), S2 (76-way `rcases` registries, the slowest
module), S3 (the same tactic block ~131 more times in five vm files), S4 (4M
heartbeats in `Wasm/Fuel.lean`, `HostInvariant.lean`), S6 (copied
rollback/settlement `let` block in four runtime files).

## 6. nearcore divergence — first run; 16 marked, 9 filed

No `nearcore divergence:` comment existed and the table was empty. The 16 clear,
intentional simplifications now carry the comment and a row in the
[divergences table](../../../notes/design/NEAR_RUNTIME.md#divergences-from-nearcore)
(b5505c3; comments only, rebuilt in section 1): counter ids, missing actions
(Delegate, global deploy, state init, gas keys), missing receipt kinds, no
`block_hash`, no signature verification cost, stake and `useGlobalContract`
unsupported, seed without `nativeReceiptHashes`, single shard, call depth instead
of `max_stack_height`, start functions, six missing v86 imports, conditional
trie-node costs, rejected crypto hosts, arbitrary block context and schedule,
one `ApplyState` across settling blocks. The stale `Metered.lean` header on
trie-node costs was corrected.

**Filed** (`divergence`, D1–D9): validation of VM-created receipts; DeleteAccount
large-state check; DeleteAccount zero-balance refund receipt (confirmed against
both sources); duplicate transactions; delay limit on gas instead of compute and
proof size; per-receipt storage proof limit; Wasm prepare limits; log limits;
oversized `value_return`. The other transition functions compared match nearcore.

## 7. Documentation — fixed

**Fixed** (f0ae1b6): the root README, `SPECIFICATIONS.md` and the w-near
verification README now name the three verification projects and the actual
refinement status; `NEAR_RUNTIME.md` names `Near.apply`; `PROJECT_STRUCTURE.md`
and `near-lean/README.md` list `interface/`; `near-lean/README.md` no longer says
there is no binary decoder; `tools/README.md` no longer describes the removed
Programs package, CI steps that don't run, or a tolerant core audit;
`notes/todo/` files lost a pasted chat path and stale status lines;
`audit-all` now includes `interface`. Blueprint: the w-near blueprint states
exactly the 15 `Spec/` items with correct status.

**Filed:** X2 (sputnik `blueprint/` folders are proof indexes, not
leanblueprint), X3 (`notes/todo/wasm_runtime_rewrite.md` is mostly history).

## 8. Tests and CI — fixed / filed

Path filters cover every current directory and name no missing path.
**Fixed** (53d0cad): the finance nearcore cache key hardcoded the revision; it
now hashes `near-lean/runtime/reference.json`; the config dump build now has a
cargo cache. **Filed:** T1 (nothing automatic builds vm/runtime/chain or the
contract projects; this check's breakages show the cost), T2–T4 (no oracle
scenario for `use_global_contract`, no runtime test of `distributedGas`, no test
of the wasm-tools version suffix), T5 (two Python regressions skipped by
`unittest discover`), X4 (nearcore SHA repeated in `runtime-reference.yml:30`).
Over-broad Lake cache keys (an iris bump invalidates vm/runtime/chain) cost time
only; not filed. Timings: SECTION8_TIMINGS

## 9. Missing features — first run; 7 filed

The main blocker: `unsupportedRuntimeHost` rejects hashing, signature, curve,
validator, yield and global-deploy hosts, and 9 of 11 dataset binaries import at
least one. Filed (`missing-feature`, F1–F7): hash hosts; signature/curve hosts as
named trusted oracles; yield/resume; checking the invariant on live state; a
shared near-sdk storage/serialization library; standard environment contract
models and cross-contract assumptions; validator view hosts. Already tracked in
`notes/`: upgrades, start functions and stack limiter, the wNEAR refinement,
generic refinement and trie-node gas, historical replay, snapshots and fuzzing,
the Comparator check, the wasm-logic milestone, pending catalog builds.

## 10. Cost

SECTION10_COST
