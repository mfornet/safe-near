# Notes reconciliation — 2026-10-20

Applied after the user removed the human-only editing restriction:

- Removed the restriction-only `notes/AGENTS.md` and its README references;
  periodic checks now update stale notes directly.
- Replaced nonexistent `docs/`, `plan/`, `sdk/`, `task/`, and `Specs/` layout
  descriptions with the current package and contract verification structure.
- Closed initial Talos/Iris, testsuite, mergesort harness, and runtime setup tasks;
  then reconciled them with newer main: all four program proofs, snapshot tools,
  CI style tooling, and shared toolchain enforcement are now implemented.
  Retained open coverage and broader validation work.
- Documented the VM/runtime/chain boundaries, modeled access keys, and current
  conformance tests. Kept history replay, upgrade safety, fuzzing, and full
  scheduling equivalence as goals requiring further work.
- Updated dataset provenance/build paths and specification extraction tooling.
- Consolidated `PROVING 2.md` into `PROVING.md` and removed the numbered copy.
  Preserved kernel/axiom policy and identified strict Comparator as proposed,
  rather than claiming it is already enforced.

The initial check results remain tied to their checked revision. The subsequent
merge brings newer code from main; its validation is recorded separately in
[merge follow-up](merge-follow-up.md).
