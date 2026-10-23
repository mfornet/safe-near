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

- Points-to assertions in `near-lean/wasm-logic` that split memory, locals
  and globals into separately owned pieces, and per-instruction rules over
  them; today the logic owns the whole store. Success criteria and the
  Iris-Wasm port that measures them:
  [wasm_logic_iris.md](todo/wasm_logic_iris.md).
- Close the model gaps listed in [Wasm runtime](design/WASM_RUNTIME.md): start
  functions, exported imports, nearcore's stack limiter.

## Code health

- Extend Lean style and formatting enforcement as packages evolve.
