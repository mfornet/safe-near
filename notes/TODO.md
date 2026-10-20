# TODO

The Talos interpreter and Iris machinery are imported, the Wasm testsuite runs,
and all four program specifications have completed correctness proofs (mergesort
proves partial correctness, allowing its specified OOM outcome). The VM, runtime,
and chain layers and independent nearcore conformance harnesses are implemented.
Remaining work:

- Complete runtime semantic coverage, conformance, and compositional runtime/chain
  invariants.
- Simplify the imported Talos code where unused functionality can safely be removed.
- Extend Lean style and validated formatting coverage as packages evolve. The
  tooling is available, and CI enforces the shared root Lean toolchain.
- Extend the existing partial-snapshot downloader and import tooling to additional
  account features and broader deployed-contract scenarios.
- Extend the existing runtime/chain scenario and independent conformance harnesses
  to broader real-chain snapshots and full scheduling equivalence, towards a
  near-workspaces-style testing environment.
