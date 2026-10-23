# TODO

Done so far: our own Wasm runtime passes the Wasm testsuite; the VM, runtime
and chain layers run on it with nearcore conformance harnesses.

## Runtime

- Complete runtime semantic coverage and conformance against nearcore.
- Prove compositional runtime/chain invariants.
- Extend scenario and conformance harnesses to real-chain snapshots and full
  scheduling equivalence, towards a near-workspaces-style test environment.
- Extend the snapshot downloader to more account features and deployed contracts.

## Contracts

- Prove the wNEAR refinement (`Refines`): the binary behaves as the model.
- Decide how to handle contract upgrades ([NEAR model](design/NEAR_MODEL.md)).

## Wasm runtime

- A separation-logic layer (Iris) over `Wasm.Exec.step`, for proofs about Wasm
  code rather than refinement at the `NearVM.run` boundary
  ([plan](todo/wasm_runtime_rewrite.md), phase 4).
- Close the model gaps listed in [Wasm runtime](design/WASM_RUNTIME.md): start
  functions, exported imports, nearcore's stack limiter.

## Code health

- Extend Lean style and formatting enforcement as packages evolve.
