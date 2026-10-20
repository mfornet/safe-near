# TODO

The Talos interpreter and Iris machinery are imported, the Wasm testsuite runs,
and the programs package includes a mergesort smoke harness. The VM, runtime,
and chain layers and independent nearcore conformance harnesses are implemented.
Remaining work:

- Complete the known program correctness proofs for byte echo, GCD and mergesort.
- Complete runtime semantic coverage, conformance, and compositional runtime/chain
  invariants.
- Simplify the imported Talos code where unused functionality can safely be removed.
- Set up a Lean linter and formatter in CI.
- Enforce a shared Lean toolchain across every Lean package.
- Build a tool to download partial NEAR blockchain snapshots for runtime tests
  against deployed contracts.
- Extend the existing runtime/chain scenario and independent conformance harnesses
  to broader real-chain snapshots and full scheduling equivalence, towards a
  near-workspaces-style testing environment.
