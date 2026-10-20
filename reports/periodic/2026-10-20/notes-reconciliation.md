# Notes reconciliation — 2026-10-20

Applied after the user removed the human-only editing restriction:

- Removed the restriction-only `notes/AGENTS.md` and its README references;
  periodic checks now update stale notes directly.
- Replaced nonexistent `docs/`, `plan/`, `sdk/`, `task/`, and `Specs/` layout
  descriptions with the current package and contract verification structure.
- Closed initial Talos/Iris, testsuite, mergesort harness, and runtime setup tasks;
  retained open proof, coverage, snapshot, and CI tooling work.
- Documented the VM/runtime/chain boundaries, modeled access keys, and current
  conformance tests. Kept history replay, upgrade safety, fuzzing, and full
  scheduling equivalence as goals requiring further work.
- Updated dataset provenance/build paths and specification extraction tooling.
- Consolidated `PROVING 2.md` into `PROVING.md` and removed the numbered copy.
  Preserved kernel/axiom policy and identified strict Comparator as proposed,
  rather than claiming it is already enforced.

These follow-up changes affect documentation only. The recorded build, proof,
conformance, and reproduction results apply to the unchanged checked code.
