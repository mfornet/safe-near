# Merge follow-up — 2026-10-20

Integrated remote `main` at `fc34915` into the periodic-check branch. The original
check started at `dbf9d11`; its counts, pins, timings, and native comparisons
remain historical results for that revision and the check fixes.

Conflict resolutions preserve newer main behavior:

- Heavy CI workflows remain opt-in. Their old automatic path filters are
  superseded by the inexpensive automatic gate, while improved cache keys remain.
- Both formatter-cache and periodic-log ignore rules are retained.
- The generated program AST import remains separate from the wide proof umbrella.
- New storage read gas charges remain intact; only the still-unused register-length
  helper is removed. Other dead-helper removals have no callers on the merged tree.
- Notes now reflect main's completed four program proofs, snapshot tools, Lean
  tooling, and shared version enforcement. The human-only restriction is removed.

The merged validation commands and exit codes are recorded in
[merge-validation.json](merge-validation.json). All 11 commands passed:

- All seven Lean packages build with `--wfail`.
- `just ci-check`: shared toolchain enforcement and 78 offline Python tests.
- `just near-test`: 103 VM, 179 runtime, and 46 chain checks, zero failures.
- `just runtime-adapter-test`: 65 adapter checks.
- `just wnear-audit`: 27 modules, 1,357 declarations, 670 theorems,
  zero axiom-policy violations.

Workflow YAML parsing, justfile formatting, local Markdown links, and
`git diff --check` also pass. Recorded command time for this merge validation is
869.23 seconds.

Expensive native comparisons and byte-for-byte reproduction from the original
check were not repeated for the newer main. Their old results must not be read as
conformance evidence for all upstream changes. Hosted CI status at the starting
revision is also historical; no billing settings were changed.
