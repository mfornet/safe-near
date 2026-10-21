# TODO

Done so far: the Wasm interpreter and Iris machinery are imported and pass the
Wasm testsuite; the VM, runtime and chain layers exist with nearcore
conformance harnesses; the four program specifications are proved (mergesort
as partial correctness, allowing its OOM outcome).

## Runtime

- Complete runtime semantic coverage and conformance against nearcore.
- Prove compositional runtime/chain invariants.
- Extend scenario and conformance harnesses to real-chain snapshots and full
  scheduling equivalence, towards a near-workspaces-style test environment.
  The [historical replay plan](todo/replay_near_history.md) tracks archive capture,
  original-trie witnesses and byte-exact chunk comparison.
- Extend the snapshot downloader to more account features and deployed contracts.

## Contracts

- Prove the wNEAR refinement (`Refines`): the binary behaves as the model.
- Decide how to handle contract upgrades ([NEAR model](design/NEAR_MODEL.md)).

## Code health

- Remove unused parts of the imported Talos code.
- Extend Lean style and formatting enforcement as packages evolve.
