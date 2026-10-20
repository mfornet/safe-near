# Periodic checks

At least once a week we should make a large check of the project. The main idea
is to check that everything is up to date, including comments, markdown files,
tests and code. We should avoid maintaining legacy code: if decisions taken
along the way made part of the code unused or suboptimal we should acknowledge
it and either record it or, preferably, fix it.

We should run the large and expensive tests that we don't run often, and make
sure they pass and are clean. If not, fix them.

The main goal of this periodic check is consolidation and simplification. We
work on large features during the week, and we need to make sure the code is
kept cohesive and consistent, not a big Frankenstein growing in multiple
directions. It is ok if the result of this check is a large refactor, as long
as the overall direction is simplification. We should avoid introducing new
concepts or features during check fixes.

Things to pay attention to:
- Dependencies / toolchains that need to be updated
- Code that we no longer use or maintain
- Obsolete comments, either inline in code or in markdown files documenting
  old decisions
- Growth of the trusted base without a written reason

## Constraints on the fixes

- Everything that builds today must still build, and CI must stay green.
- No new `sorry`. The number of `sorry`s may only go down.
- Spec statements (`Spec/` in each verification project) do not change meaning. Renaming
  or moving is fine; weakening or strengthening a theorem is a feature, not a
  check fix.
- The trusted base (axioms, `native_decide`, `partial`, `unsafe`,
  `implemented_by`, the Wasm interpreter, the runtime adapter) does not grow.
  If it has to, the reason is written down in the report.
- Pinned versions move only on purpose. Updating a pin is a conscious decision
  recorded in the report, never a side effect of a fix.

## Checklist

Every check runs through all sections. Each section ends either with "clean"
or with a list of findings, and each finding is either fixed in the same check
or recorded in the report with a reason for leaving it.

### 1. Build and tests

Baseline, must be clean (no warnings, no `sorry` outside the known list):

    just build-all
    just near-build
    just near-test
    just runtime-adapter-test

Expensive tests that are not run daily. They need a pinned nearcore checkout
(same commit as in `.github/workflows/runtime-reference.yml`):

    just near-conformance
    just near-finance-conformance <checkout>
    just near-nonce-conformance <checkout>
    just near-allowance-conformance <checkout>
    just wnear-audit
    just blueprint w-near
    just reproduce w-near

The Wasm testsuite report (`testsuite_report.txt`) must match what CI checks.
Any failure here is fixed before anything else in the check.

### 2. Trusted base

Produce the numbers and compare them with the previous report:
- `sorry` count per package and per contract (`just sorries <contract>`)
- Axioms used transitively beyond `propext`, `Classical.choice`, `Quot.sound`
  (`audit/wnear.json` from `just wnear-audit`)
- Occurrences of `native_decide`, `partial`, `unsafe`, `implemented_by`,
  `opaque` with no definition, and `set_option maxHeartbeats`
- Anything trusted by convention: the Wasm interpreter, the runtime adapter,
  the conformance comparison scripts, the config dump

Every number that went up needs a sentence explaining why.

### 3. Pinned versions

List the pins and decide for each one: keep or update.
- Lean toolchain in every `lean-toolchain` of `near-lean/*` and
  `contracts/*/verification`. They must all be identical.
- Mathlib / other lake dependencies (`lake-manifest.json`)
- nearcore commit: in both CI workflows and in `tools/runtime-*-reference`
- Rust toolchain used to build the reference adapters
- GitHub Actions versions in `.github/workflows`
- On-chain contract hashes in `contracts/*/contract.toml`

If a pin is updated, the whole of section 1 is rerun afterwards.

### 4. Dead and duplicated code

- Lean declarations not referenced anywhere (search by name across the
  workspace; declarations only used by their own tests count as suspicious)
- Modules not imported by anything
- justfile recipes nobody runs, scripts in `tools/` nobody calls, CI steps
  that test nothing anymore
- Duplicated helpers between `near-lean/*` packages and between contracts
- Untracked or stray files in the tree (`git status`), leftover copies such
  as `FILE 2.md`, generated outputs that should be regenerated instead of
  committed

Delete first, record only when deletion is not possible yet.

### 5. Documentation and comments

- Every markdown file under `notes/` describes the current architecture:
  folder names, component boundaries, interfaces, commands. Report every
  stale sentence and update it to match the implementation.
- Inline comments and docstrings in Lean match what the code does now.
- The blueprint (`contracts/*/verification/blueprint`) states exactly the
  theorems that exist in `Spec/`, nothing more and nothing less, and the
  proof status it shows matches reality.
- `README.md` at the root and `justfile` help texts are accurate.
- TODO files: close what is done, delete what no longer applies.

### 6. CI health

- Path filters in the workflows cover every directory that exists today
- Cache keys still key on the right files
- Timeouts and build times: note the wall time of each job and of each
  `lake build`. A step that doubled since the last check is a finding.
- Slow proofs: anything with raised `maxHeartbeats` or visibly slow to
  elaborate is a candidate for simplification

### 7. Report

Write a short dated report with: the numbers from section 2, the pins from
section 3, every finding with its resolution (fixed / recorded / requires maintainer action), and the total cost of the agent runs. Keep reports next to each other
so the next check can diff against the previous one.

## Driving the check with agents

The check is mostly reading and comparing, which is a good fit for agents, but
it touches the whole repository and can burn a lot of tokens if done naively.
Rules of thumb:

- One coordinator runs the checklist and owns the report. It does not read
  the whole codebase itself; it delegates sections and merges results.
- Fan out by section, not by file. Sections 2, 3, 4, 5 and 6 are independent
  and can run in parallel. Section 1 runs first because its failures change
  what the others should look at.
- Each delegated agent gets a narrow brief: the section, the commands to run,
  the files to look at, and the exact shape of the answer expected (a list of
  findings with file and line). Agents that are told "look for anything
  wrong" read everything and report noise.
- Prefer deterministic tooling over agent reading whenever it exists:
  `grep` for `sorry` and the trusted-base keywords, the axiom audit, `git
  status`, `lake build` warnings. Agents interpret the output; they do not
  reproduce it by hand.
- Use cheaper and faster models for mechanical sections (3, 4, 6) and the
  strongest model only where judgement is needed: deciding whether a refactor
  simplifies, and reviewing proposed changes to proofs.
- Fixes are applied by one agent at a time per package. Parallel edits to the
  same Lean package produce conflicts and broken builds that cost more than
  the time saved.
- Every proposed deletion or refactor is verified by a full rebuild before it
  is accepted. A delegated agent reports "builds" only when it ran the build.
- Record the token or dollar cost of the check in the report. If a check
  costs noticeably more than the previous one, the checklist or the briefs
  need tightening, not the budget.
