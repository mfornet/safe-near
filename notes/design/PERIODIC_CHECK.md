# Periodic checks

Once a week, review the whole project for consolidation and simplification.
Features land during the week; this check keeps the code cohesive instead of
growing in every direction. A large refactor is a fine outcome if it simplifies.
Don't add new features or concepts as part of the check.

Look for:
- Outdated dependencies and toolchains.
- Unused or unmaintained code. Prefer deleting it to documenting it.
- Stale comments and notes.
- Growth of the trusted base without a written reason.

## Rules for fixes

- Everything that builds today still builds, and CI stays green.
- No new `sorry`.
- `Spec/` statements keep their meaning. Renaming or moving is fine; weakening
  or strengthening a theorem is a feature, not a fix.
- The trusted base (axioms, `native_decide`, `partial`, `unsafe`,
  `implemented_by`, the Wasm interpreter, the runtime adapter) does not grow
  unless the report says why.
- Pins change only on purpose, recorded in the report.

## Checklist

Each section ends with "clean" or a list of findings. Each finding is fixed in
the same check or recorded in the report with a reason.

### 1. Build and tests

`just periodic-check-plan` shows what the runner will do; `just periodic-check
<nearcore-checkout>` runs it and saves logs and timings under `audit/periodic/`.
The checkout must be at the nearcore commit pinned in
`.github/workflows/runtime-reference.yml`.

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

### 2. Trusted base

Compare with the previous report and explain every number that went up:
- `sorry` count per package and contract (`just sorries <contract>`).
- Axioms beyond `propext`, `Classical.choice`, `Quot.sound` (`audit/wnear.json`).
- `native_decide`, `partial`, `unsafe`, `implemented_by`, bodiless `opaque`,
  `set_option maxHeartbeats`.
- Code trusted by convention: the interpreter, the runtime adapter, the
  conformance scripts, the config dump.

### 3. Pinned versions

Keep or update each, and rerun section 1 after any update:
- `lean-toolchain` in every package (all identical).
- Lake dependencies (`lake-manifest.json`).
- nearcore commit in CI workflows and `tools/runtime-*-reference`.
- Rust toolchain for the reference adapters.
- GitHub Actions versions.
- Contract hashes in `contracts/*/contract.toml`.

### 4. Dead and duplicated code

- Unreferenced Lean declarations (only used by their own tests is suspicious).
- Modules nobody imports.
- Unused justfile recipes, `tools/` scripts and CI steps.
- Helpers duplicated across packages or contracts.
- Stray files (`git status`, copies like `FILE 2.md`, committed generated output).

### 5. Documentation

- `notes/` matches the current code: folders, boundaries, commands.
- Lean comments and docstrings match the code.
- Each blueprint states exactly the theorems in `Spec/`, with correct status.
- The root `README.md` and justfile help texts are accurate.
- `TODO.md`: remove what is done or no longer applies.

### 6. CI health

- Workflow path filters cover every current directory.
- Cache keys depend on the right files.
- Job and `lake build` times; anything that doubled is a finding.
- Slow proofs or raised `maxHeartbeats` are candidates for simplification.

### 7. Report

Write a dated report in `reports/periodic/` with the numbers from section 2,
the pins from section 3, every finding and its resolution (fixed, recorded, or
needs maintainer action), and the cost of the agent runs.

## Running the check with agents

- One coordinator owns the report and delegates sections; it does not read the
  whole codebase.
- Run section 1 first, then sections 2 to 6 in parallel.
- Give each agent a narrow brief: commands, files, and the expected answer
  format (findings with file and line). "Look for anything wrong" produces noise.
- Prefer tools (`grep`, the axiom audit, `git status`, build warnings) to
  reading by hand.
- Use cheaper models for mechanical sections (3, 4, 6) and the strongest model
  for judgement calls and proof changes.
- One agent edits a given Lean package at a time.
- Accept a change only after a full rebuild that the agent actually ran.
- If a check costs noticeably more than the last one, tighten the briefs.
