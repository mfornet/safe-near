# Periodic checks

Every so often, review the whole project for consolidation and simplification.
Features land in between; this check keeps the code cohesive instead of growing
in every direction. A large refactor is a fine outcome if it simplifies.
Don't implement new features or concepts as part of the check; propose them
instead (section 9).

Look for:
- Outdated dependencies and toolchains.
- Unused or unmaintained code. Prefer deleting it to documenting it.
- Stale comments and notes.
- Simplifications of nearcore that the code does not acknowledge.
- Growth of the trusted base without a written reason.

Start a check with `/periodic-check` in a Claude Code session
(`.claude/skills/periodic-check/SKILL.md`); this file is what it follows.

## Which sections are due

`reports/periodic/LEDGER.json` records, per section, the commit it was last
checked at, the report (a Linear issue) and the Linear issues it filed. `just periodic-due`
lists the sections whose watched paths changed since then (the path map is
`SECTIONS` in `tools/periodic_check.py`); pins are due by age instead, once a
week. Only due sections run. If nothing is due, there is no check.

After a check, record what it covered:

    python3 tools/periodic_check.py --record <section>... --report <review issue URL> --issue SAF-27 --issue SAF-28

## Rules for fixes

- Everything that builds today still builds, and CI stays green.
- No new `sorry`.
- `Spec/` statements keep their meaning. Renaming or moving is fine; weakening
  or strengthening a theorem is a feature, not a fix.
- The trusted base (axioms, `native_decide`, `partial`, `unsafe`,
  `implemented_by`, the Wasm interpreter, the runtime adapter) does not grow
  unless the report says why.
- Pins change only on purpose, recorded in the report.
- Changes to the Wasm runtime also pass `near-lean/wasm/testsuite_report.txt`
  (zero `fail`), `just near-test` and `just near-conformance`.

## Checklist

Each section ends with "clean" or a list of findings. Each finding is fixed in
the same check or filed in Linear (see [Findings in Linear](#findings-in-linear)).
The ledger name of each section is in parentheses.

### 1. Build and tests (`build`)

`just periodic-check-plan` shows what the runner will do; `just periodic-check
<nearcore-checkout>` runs it and saves logs and timings under `audit/periodic/`.
The checkout must be at the nearcore commit pinned in
`near-lean/runtime/reference.json`.

Baseline, no warnings and no `sorry` outside the known list:

    just ci-check
    just build-all
    just near-build
    just near-test
    just runtime-adapter-test

Expensive, not run daily:

    just near-conformance
    just near-finance-conformance <checkout>
    just near-nonce-conformance <checkout>
    just near-allowance-conformance <checkout>
    just near-receipt-conformance <checkout>
    just wnear-audit
    just blueprint w-near
    just reproduce w-near

`testsuite_report.txt` must match what CI checks. Fix failures here first.

### 2. Trusted base (`trusted-base`)

Compare with the previous report and explain every number that went up:
- `sorry` count per package and contract (`just sorries <contract>`).
- Axioms beyond `propext`, `Classical.choice`, `Quot.sound` (`audit/wnear.json`).
- `native_decide`, `partial`, `unsafe`, `implemented_by`, bodiless `opaque`,
  `set_option maxHeartbeats`.
- Code trusted by convention: the interpreter, the runtime adapter, the
  conformance scripts, the config dump.

### 3. Pins and upgrades (`pins`)

Keep or update each, and rerun section 1 after any update:
- `lean-toolchain` in every package (all identical).
- Lake dependencies (`lake-manifest.json`).
- nearcore commit in CI workflows and `tools/runtime-*-reference`.
- Rust toolchain for the reference adapters.
- GitHub Actions versions.
- Contract hashes in `contracts/*/contract.toml`.

Try the newest Lean toolchain and Mathlib/Iris on a branch with the full
section 1 plan. Land it if everything stays green; otherwise file the blocker
(`upgrade`).

### 4. Dead and duplicated code (`dead-code`)

- Unreferenced Lean declarations (only used by their own tests is suspicious).
- Modules nobody imports.
- Unused justfile recipes, `tools/` scripts and CI steps.
- Helpers duplicated across packages or contracts that a shared definition
  would make simpler, not just shorter.
- Stray files (`git status`, copies like `FILE 2.md`, committed generated output).

### 5. Simplification and compile cost (`simplification`)

- Rank modules by `lake build` time from the evidence of section 1; the slowest
  ones and any raised `maxHeartbeats` are the first candidates.
- Shorten proofs that are long for what they prove (repeated case splits,
  copied lemma bodies, `simp` sets that can be named once).
- Every change rebuilds the affected packages and keeps `Spec/` meaning.

### 6. nearcore divergence (`divergence`)

Review the changes in `near-lean/{vm,runtime,chain}` since the last check
against nearcore at the pinned revision in `near-lean/runtime/reference.json`.
Every place that simplifies or omits nearcore behavior must carry a
`nearcore divergence:` comment saying what differs and why, and have a row in
the [divergences table](NEAR_RUNTIME.md#divergences-from-nearcore). An unmarked
simplification is a finding: mark it, or file it (`divergence`) when the right
behavior is unclear.

### 7. Documentation (`docs`)

- `notes/` matches the current code: folders, boundaries, commands.
- Lean comments and docstrings match the code; remove comments that only
  restate it.
- Each blueprint states exactly the theorems in `Spec/`, with correct status.
- The root `README.md` and justfile help texts are accurate.
- `TODO.md`: remove what is done or no longer applies.

### 8. Tests and CI (`tests-ci`)

- Workflow path filters cover every current directory.
- Cache keys depend on the right files.
- Job and `lake build` times; anything that doubled is a finding.
- Test value: from the `summary.json` files under `audit/periodic/`, find slow
  suites that never fail and that other suites already cover, and behavior
  (divergences, recent fixes) that no test covers. Propose removing or adding
  tests (`test-coverage`); don't change what CI runs inside the check.

### 9. Missing features (`features`)

Propose only. Read `notes/TODO.md`, the design notes and the divergences
table, and file each important gap that isn't tracked yet (`missing-feature`):
what is missing, why it matters for verifying deployed contracts, and where it
would go.

### 10. Report

Reports live in Linear, not in the repository. Open a review issue in the
Safe-near team, "Review periodic check <date> findings" (label
`periodic-check`, assigned to the maintainer), and attach the report to it as
a document: the numbers from section 2, the pins from section 3, every finding
and its resolution (fixed, filed with its Linear ID, or needs maintainer
action), the sections that were skipped as not due, and the cost of the agent
runs. Filed findings are sub-issues of the review issue. Then update the
ledger, the only file the report adds to the repository. Build logs and
evidence stay in the ignored `audit/periodic/`.

## Findings in Linear

Findings that aren't fixed in the check become issues in the Safe-near team,
labeled `periodic-check` and one of `divergence`, `missing-feature`,
`simplification`, `stale`, `test-coverage`, `upgrade`. Before filing, search
the open issues with the same label; comment on an existing issue instead of
opening a duplicate. File new issues in Backlog as sub-issues of the review
issue (see section 10). Each issue names the files and lines, and the commit the
check ran at.

## Running the check with agents

- One coordinator owns the report and delegates sections; it does not read the
  whole codebase.
- Run section 1 first, then the other due sections in parallel.
- Give each agent a narrow brief: commands, files, and the expected answer
  format (findings with file and line). "Look for anything wrong" produces noise.
- Prefer tools (`grep`, the axiom audit, `git status`, build warnings) to
  reading by hand.
- Use cheaper models for mechanical sections (3, 4, 8) and the strongest model
  for judgement calls (5, 6, 9) and proof changes.
- One agent edits a given Lean package at a time.
- Accept a change only after a full rebuild that the agent actually ran.
- If a check costs noticeably more than the last one, tighten the briefs.
